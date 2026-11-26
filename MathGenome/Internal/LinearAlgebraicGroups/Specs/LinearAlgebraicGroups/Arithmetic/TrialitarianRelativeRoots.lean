import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianPinnedBorelPair
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RankTwoRootSystems

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianRelativeRoots

open AbstractPairing (Root)
open AdjointRepresentation (GroupPoints)
open AbsoluteDynkinTypes (D4Cartan D4Outer)
open BorelProper (IsParabolic)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character Cocharacter)
open GeometricBorelConjugacy (IsQuasiSplit subgroupOfSubgroup)
open GeometricRadicals (IsSemisimple baseChangedSubgroup)
open Pinning (AttachedDatum Pinning SimpleRoot)
open QuasiSplitOrbitLevis (IsAmbientPinnedAction MultiplicativeComparison SplitPairOver)
open QuasiSplitPinnedPairModel (BorelPair)
open RankOneFlag (SameSubgroup)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (relativeRoots)
open Relative.RelativeWeylScheme (QuotientData rationalProjection)
open RootGroups (AdditiveLine rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open StandardParabolicLevi (IsContractingRadical)
open TrialitarianLocalForms (IsTrialitarian)
open TrialitarianPinnedBorelPair (underlyingAction)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition bigCellMap
  oppositeCocharacter)

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

/-- Coordinates sum the outer coefficients in the numbering of the shared
D₄ diagram, in which vertex 1 is central. -/
def project (c : Fin 4 → ℤ) : ℤ × ℤ := (c 0 + c 2 + c 3, c 1)

def positiveCoordinates : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (1, 1), (2, 1), (3, 1), (3, 2)}

/-- The long coordinates in the short-root/long-root basis of G₂. -/
def longCoordinates : Finset (ℤ × ℤ) :=
  {(0, 1), (3, 1), (3, 2), (0, -1), (-3, -1), (-3, -2)}

section Splitting

variable (K : Type u) [Field K] [Algebra F K]

/-- A realization of the rational Borel pair in the actual split scalar extension. -/
abbrev AbsolutePair (M : BorelPair G) := SplitPairOver (K := K) G M.torus M.positive

variable {K}

/-- The map of characters given by restriction to the base change of the
rational split subtorus and descent of that split torus's characters. -/
def IsRestriction {M : BorelPair G} (S : ClosedSubgroup M.torus.group)
    (t : QuasiSplitFixedWeyl.multiplicativeGroup K ≅
      (groupBaseChange F K).obj (QuasiSplitFixedWeyl.multiplicativeGroup F))
    (restrict : Character ((groupBaseChange F K).obj M.torus.group) →* Character S.group) :
    Prop :=
  ∀ χ, (groupBaseChange F K).map (restrict χ) =
    (groupBaseChange F K).map S.inclusion ≫ χ ≫ t.hom

/-- The absolute Galois action preserves the split pinning semilinearly.
The additive coordinate is compared to the standard affine coordinate
over the ground field. -/
def IsDescendedPinning {M : BorelPair G} (P : AbsolutePair K M)
    (D : AttachedDatum P.pair) (A : AdditiveLine K)
    (U : OrderedRootProducts.RootSubgroupFamily P.pair.T) (pin : Pinning A P.pair U)
    (t : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased) : Prop :=
  ∃ (A₀ : AdditiveLine F) (e : (groupBaseChange F K).obj A₀.group ≅ A.group),
    (∀ (R : TestAlgebra K) (a : R),
      baseChangePoint F K A₀.group.X R (rootPoint e.inv R a) =
        rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) a) ∧
    IsAmbientPinnedAction D pin e t ω

/-- Root coordinates and the full fibre calculation on the actual
absolute and relative characters. -/
def Folding {M : BorelPair G} (S : ClosedSubgroup M.torus.group)
    (P : AbsolutePair K M) (D : AttachedDatum P.pair)
    (simple : letI := D.comm; Fin 4 ≃ D.base.support)
    (restrict : Character P.pair.T.group →* Character S.group)
    (coeff : Root P.pair.T → Fin 4 → ℤ) (coord : (ℤ × ℤ) →+ Additive (Character S.group)) :
    Prop :=
  letI := D.comm
  (∀ α, D.datum.rootDatum.root α =
    ∑ i, coeff α i • D.datum.rootDatum.root (simple i).val) ∧
  (∀ α, coord (project (coeff α)) = Additive.ofMul (restrict α.val)) ∧
  (∀ i, restrict (simple i).val.val =
    Additive.toMul (coord (if i = 1 then (0, 1) else (1, 0)))) ∧
  Function.Injective coord ∧
  (∀ α : Root P.pair.T, restrict α.val ≠ 1) ∧
  relativeRoots (subgroupOfSubgroup M.torus S) =
    Set.range (fun α : Root P.pair.T ↦ restrict α.val) ∧
  (fun α ↦ project (coeff α)) '' subgroupRoots P.pair.T P.pair.B =
    (positiveCoordinates : Set (ℤ × ℤ)) ∧
  Set.range (fun α ↦ project (coeff α)) =
    (LieAlgebrasAndRepresentations.rankTwoCoefficients .G₂ : Set (ℤ × ℤ)) ∧
  Nat.card {α // project (coeff α) = (1, 0)} = 3 ∧
  Nat.card {α // project (coeff α) = (0, 1)} = 1 ∧
  Nat.card {α // project (coeff α) = (1, 1)} = 3 ∧
  Nat.card {α // project (coeff α) = (2, 1)} = 3 ∧
  Nat.card {α // project (coeff α) = (3, 1)} = 1 ∧
  Nat.card {α // project (coeff α) = (3, 2)} = 1 ∧
  (∀ p ∈ longCoordinates, ∃! α, project (coeff α) = p)

end Splitting

/-- An embedded split SL₂ with its two elementary subgroups and its
diagonal cocharacter in the original split torus. The matrix identifications
are on all test algebras, including those with nilpotents. -/
abbrev RankOne (S : ClosedSubgroup G.val) := TrialitarianFixedRootSL2.RankOne S

/-- The cocharacter of the embedded diagonal and its inverse define proper
opposite rational parabolics and contract their respective radicals. -/
def RankOne.HasOppositeRadicals {S : ClosedSubgroup G.val} (L : RankOne S) : Prop :=
  let c := L.cochar ≫ S.inclusion
  ∃ (P : LimitDecomposition c) (Q : LimitDecomposition (oppositeCocharacter c)),
    IsParabolic G P.parabolic ∧ IsParabolic G Q.parabolic ∧
    ¬ IsIso P.parabolic.inclusion ∧ ¬ IsIso Q.parabolic.inclusion ∧
    SameSubgroup P.centralizer Q.centralizer ∧ IsOpenImmersion (bigCellMap P Q).left ∧
    IsContractingRadical P ∧ IsContractingRadical Q ∧
    IsSubgroupOf L.positive P.contracting ∧ IsSubgroupOf L.negative Q.contracting

/-- A maximal rational standard parabolic whose unipotent radical contains
the upper subgroup centrally, with centrality on all test algebras. -/
def RankOne.HasCentralUpper {S : ClosedSubgroup G.val} (L : RankOne S)
    (B : ClosedSubgroup G.val) : Prop :=
  ∃ (P : ClosedSubgroup G.val) (U : ClosedSubgroup P.group),
    IsParabolic G P ∧ IsSubgroupOf B P ∧ ¬ IsIso P.inclusion ∧
    (∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf P Q →
      IsSubgroupOf Q P ∨ IsIso Q.inclusion) ∧
    GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P) U ∧
    IsSubgroupOf L.positive (subgroupOfSubgroup P U) ∧
    ∀ (R : TestAlgebra F) (x : GroupPoints L.positive.group R) (y : GroupPoints U.group R),
      Commute (x ≫ L.positive.inclusion.hom.hom : GroupPoints G.val R)
        (y ≫ U.inclusion.hom.hom ≫ P.inclusion.hom.hom : GroupPoints G.val R)

section AbsoluteRankOne

variable {K : Type u} [Field K] [Algebra F K] {M : BorelPair G}

/-- The ground-field elementary subgroups extend to the unique two
opposite absolute root subgroups, and the split diagonal extends to the
attached absolute coroot. A splitting functional records its primitivity
in the absolute cocharacter lattice. -/
def RankOne.MatchesAbsolute (S : ClosedSubgroup M.torus.group)
    (L : RankOne (subgroupOfSubgroup M.torus S)) (P : AbsolutePair K M)
    (D : AttachedDatum P.pair) (U : OrderedRootProducts.RootSubgroupFamily P.pair.T)
    (t : QuasiSplitFixedWeyl.multiplicativeGroup K ≅
      (groupBaseChange F K).obj (QuasiSplitFixedWeyl.multiplicativeGroup F))
    (α β : Root P.pair.T) : Prop :=
  letI := D.comm
  D.datum.rootDatum.root β = -D.datum.rootDatum.root α ∧
  (∃ hp hn,
    SameSubgroup (baseChangedSubgroup K L.positive hp) (U α).val ∧
    SameSubgroup (baseChangedSubgroup K L.negative hn) (U β).val) ∧
  let c : Cocharacter P.pair.T.group := t.hom ≫
    (groupBaseChange F K).map (L.cochar ≫ S.inclusion)
  Additive.ofMul c = D.datum.rootDatum.coroot α ∧
  ∃ f : Additive (Cocharacter P.pair.T.group) →ₗ[ℤ] ℤ, f (Additive.ofMul c) = 1

/-- The descended upper coordinate at the fixed simple root agrees with
the given absolute pin on the splitting field. -/
def RankOne.MatchesPin {S : ClosedSubgroup G.val} (L : RankOne S) (P : AbsolutePair K M)
    {A : AdditiveLine K} {U : OrderedRootProducts.RootSubgroupFamily P.pair.T}
    (pin : Pinning A P.pair U) (α : SimpleRoot P.pair) : Prop :=
  ∀ (R : TestAlgebra K) (a : R),
    baseChangePoint F K G.val.X R (rootPoint
      ((pin α).val.hom ≫ (U α.val).val.inclusion) R a) =
    rootPoint (L.upper.hom ≫ L.positive.inclusion) ((restrictTestAlgebra F K).obj R) a

end AbsoluteRankOne

/-- The chosen rational Weyl representative conjugates the embedded SL₂
itself, with the matrix markings unchanged. -/
def RankOne.IsTransport {S : ClosedSubgroup G.val} (L H : RankOne S)
    (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) : Prop :=
  ∃ e : L.group.val ≅ H.group.val,
    ((groupPointsFunctor F).mapIso e) ≪≫ H.matrix = L.matrix ∧
    let n := toUnit L.group.val.X ≫ g
    (e.hom ≫ H.embedding).hom.hom = n * L.embedding.hom.hom * n⁻¹

/-- The relative-root and rank-one conclusions for a quasi-split simply
connected trialitarian D₄ group over a nonarchimedean local field. -/
def Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F),
    IsSemisimple G → GeometricallySimplyConnected G → IsTrialitarian G → IsQuasiSplit G →
    ∃ (M : BorelPair G) (S : ClosedSubgroup M.torus.group),
      QuasiSplitFixedWeyl.IsLargestSplitSubtorus S ∧
      let S₀ := subgroupOfSubgroup M.torus S
      IsMaximalSplitTorus S₀ ∧
      ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
        (_ : IsGalois F K) (P : AbsolutePair K M) (D : AttachedDatum P.pair),
        letI := D.comm
        ∃ (A : AdditiveLine K) (U : OrderedRootProducts.RootSubgroupFamily P.pair.T)
        (pin : Pinning A P.pair U)
        (simple : Fin 4 ≃ D.base.support) (ω : Gal(K/F) →* Aut D.toBased)
        (t : MultiplicativeComparison F K),
        let ρ := underlyingAction D ω
        QuasiSplitFixedWeyl.IsUnitComparison t ∧
        QuasiSplitFixedWeyl.IsScalarAction M.torus P.torusClosed D.comm D.datum t ρ ∧
        IsDescendedPinning P D A U pin t ω ∧
        (∀ i j, D.datum.rootDatum.pairing (simple j).val (simple i).val = D4Cartan i j) ∧
        (∀ σ, (ρ σ).indexEquiv (simple 1).val = (simple 1).val) ∧
        (∀ i j : D4Outer, ∃ σ : Gal(K/F), (ρ σ).indexEquiv (simple i.val).val =
          (simple j.val).val) ∧
        ∃ (restrict : Character P.pair.T.group →* Character S.group)
          (coeff : Root P.pair.T → Fin 4 → ℤ)
          (coord : (ℤ × ℤ) →+ Additive (Character S.group)),
          IsRestriction S t restrict ∧ Folding S P D simple restrict coeff coord ∧
          let α := (simple 1).val
          ∃ (αneg θ θneg : Root P.pair.T) (L H : RankOne S₀),
            project (coeff α) = (0, 1) ∧ project (coeff θ) = (3, 2) ∧
            L.MatchesAbsolute S P D U t α αneg ∧ H.MatchesAbsolute S P D U t θ θneg ∧
            L.MatchesPin P pin ⟨α, (D.simple_iff α).mp (simple 1).property⟩ ∧
            (∃ (Q : QuotientData S₀) (w : Q.splitImage.labels)
              (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X),
              rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
              w.val (restrict α.val) = restrict θ.val ∧
              L.IsTransport H (n ≫ Q.normalizer.inclusion.hom.hom)) ∧
            H.HasOppositeRadicals ∧ H.HasCentralUpper M.positive

end

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianRelativeRoots
