import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.AlgebraicCovering
import Mathlib.Topology.Connected.PathConnected

/-! Independent obligations for paper.tex:3689–3702 (the transitivity and
connectedness part of `d12:21:transitivity`). The polynomial is the original
irreducible element of ℂ[z][w]. Neither irreducibility over ℂ(z) nor any
connectedness or orbit rationality certificate is assumed. The curve and germs
are exactly those of the accepted algebraic covering interface. -/

noncomputable section
open Set
namespace Specs.D12Complex.Ch21.MonodromyTransitive
open _root_.D12Complex _root_.D12Complex.AlgebraicCovering

/-- The actual monodromy witness, including terminal continuation of every
root germ. This is the full witness from the algebraic-covering theorem. -/
def IsRootMonodromy (P : Polynomial (Polynomial ℂ)) (a : Base P)
    (M : Path a a → Equiv.Perm (RootGerm P (a : ℂ))) : Prop :=
  (∀ γ η, γ.Homotopic η → M γ = M η) ∧
  (∀ γ, M γ.symm = (M γ)⁻¹) ∧
  (∀ γ η, M (γ.trans η) = M η * M γ) ∧
  ∀ γ g, ∃ Φ : GermFamily (fun t => (γ t : ℂ)),
    IsContinuation (baseSet P) (fun t => (γ t : ℂ))
      ((congrArg Subtype.val γ.source).symm ▸ g.val) Φ ∧
    (∀ t, IsRootGerm P (γ t : ℂ) (Φ t)) ∧
    (congrArg Subtype.val γ.target ▸ Φ 1) = (M γ g).val

/-- Every actual root-germ action is transitive at every ordinary basepoint. -/
def every_monodromy_transitive_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → ∀ a : Base P,
    ∀ M : Path a a → Equiv.Perm (RootGerm P (a : ℂ)),
      IsRootMonodromy P a M →
      ∀ g h : RootGerm P (a : ℂ), ∃ γ : Path a a, M γ g = h

/-- Existence of the transitive action with all continuation and group laws. -/
def monodromy_transitive_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d → ∀ a : Base P,
    ∃ M : Path a a → Equiv.Perm (RootGerm P (a : ℂ)),
      IsRootMonodromy P a M ∧
      ∀ g h : RootGerm P (a : ℂ), ∃ γ : Path a a, M γ g = h

/-- Both connectedness conclusions concern the literal subspace of ℂ²,
with nonemptiness included by Mathlib's classes. -/
def connected_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
      PathConnectedSpace (Curve P) ∧ ConnectedSpace (Curve P)

end Specs.D12Complex.Ch21.MonodromyTransitive
