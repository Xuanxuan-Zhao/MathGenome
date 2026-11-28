import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

set_option autoImplicit false

open Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.SchubertFiniteJetActionsSpecs

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs

/-- The positive-loop action on an actual reduced Schubert space factors through
jets modulo `t^(k+1)` as soon as `difference ab - 1 ≤ k`. The actions are continuous
for the coefficient and analytic topologies and are compatible under reduction. -/
def SchubertFiniteJetActions : Prop :=
  (∀ k : ℕ, IsOpenEmbedding
    (fun g : GLJets 2 (k + 1) (Nat.succ_pos k) ↦ jetMatrixCoefficients g.val)) →
  (∀ ⦃k l : ℕ⦄ (h : k ≤ l),
    @Continuous (GLJets 2 (l + 1) (Nat.succ_pos l)) (GLJets 2 (k + 1) (Nat.succ_pos k))
      (glJetTopology 2 (l + 1) (Nat.succ_pos l)) (glJetTopology 2 (k + 1) (Nat.succ_pos k))
      (Matrix.GeneralLinearGroup.map (n := Fin 2) (truncateJet (Nat.succ_le_succ h)))) →
  ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
    ∃ ρ : ∀ (k : ℕ), difference ab - 1 ≤ k →
        MulAction (GLJets 2 (k + 1) (Nat.succ_pos k)) (SchubertSpace ab N hN),
      (∀ (k : ℕ) (hk : difference ab - 1 ≤ k),
        Continuous (fun x : GLJets 2 (k + 1) (Nat.succ_pos k) × SchubertSpace ab N hN ↦
          (ρ k hk).smul x.1 x.2)) ∧
      (∀ ⦃k l : ℕ⦄ (h : k ≤ l) (hk : difference ab - 1 ≤ k)
          (g : GLJets 2 (l + 1) (Nat.succ_pos l)) (p : SchubertSpace ab N hN),
        (ρ k hk).smul (Matrix.GeneralLinearGroup.map (truncateJet (Nat.succ_le_succ h)) g) p =
          (ρ l (hk.trans h)).smul g p) ∧
      (∀ (k : ℕ) (hk : difference ab - 1 ≤ k) (g : GLJets 2 (k + 1) (Nat.succ_pos k))
          (p : SchubertSpace ab N hN) (i : OrbitIndex ab),
        (ρ k hk).smul g p ∈ orbitPoints ab N hN i ↔ p ∈ orbitPoints ab N hN i) ∧
      (∀ (k : ℕ) (hk : difference ab - 1 ≤ k) (g : GL (Fin 2) O)
          (p : SchubertSpace ab N hN) (L : BoundedLattice 2 N),
        schubertPointSubspace p = boundedSubspace L →
          schubertPointSubspace ((ρ k hk).smul (reduceGL 2 (k + 1) (Nat.succ_pos k) g) p) =
            latticeSubspace (-(N : ℤ)) (2 * N) (positiveGLMap 2 g • L.val)) ∧
      (∀ (k : ℕ) (hk : difference ab - 1 ≤ k) (hw : 2 * N ≤ k + 1)
          (g : GLJets 2 (k + 1) (Nat.succ_pos k)) (p : SchubertSpace ab N hN),
        schubertPointSubspace ((ρ k hk).smul g p) =
          (schubertPointSubspace p).map (windowJetLinear (-(N : ℤ)) hw g.val))

end RepTheorySurvey.Geometric.SchubertFiniteJetActionsSpecs
