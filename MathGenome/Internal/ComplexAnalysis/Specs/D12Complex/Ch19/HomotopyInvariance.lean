import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation

/-!
Independent statement of paper.tex:3230–3242, d12:19-05.
The first square coordinate is path time and the second is homotopy time.
Existence is required separately for every slice, including all intermediate
slices. Equality is equality of holomorphic germs, transported into the common
fibre at `b`, and quantifies over arbitrary continuations of both slices.
-/

noncomputable section
namespace Specs.D12Complex.Ch19.HomotopyInvariance
open _root_.D12Complex

def homotopy_invariance_type : Prop :=
  ∀ (Ω : Set ℂ) (a b : ℂ) (H : unitInterval × unitInterval → ℂ),
    IsDomain Ω → Continuous H → (∀ p, H p ∈ Ω) →
    ∀ (h0 : ∀ s, H (0, s) = a) (h1 : ∀ s, H (1, s) = b)
      (φ : HolomorphicGerm a),
    (∀ s, ∃ Φ : GermFamily (fun t => H (t, s)),
      IsContinuation Ω (fun t => H (t, s)) ((h0 s).symm ▸ φ) Φ) →
    ∀ (s r : unitInterval)
      (Φ : GermFamily (fun t => H (t, s)))
      (Ψ : GermFamily (fun t => H (t, r))),
      IsContinuation Ω (fun t => H (t, s)) ((h0 s).symm ▸ φ) Φ →
      IsContinuation Ω (fun t => H (t, r)) ((h0 r).symm ▸ φ) Ψ →
      Eq.mp (congrArg HolomorphicGerm (h1 s)) (Φ 1) =
        Eq.mp (congrArg HolomorphicGerm (h1 r)) (Ψ 1)

end Specs.D12Complex.Ch19.HomotopyInvariance
