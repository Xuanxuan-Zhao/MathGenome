import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Naturality
import Mathlib.Algebra.Colimit.Module
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! KD-19, first assertion. A directed ring colimit is represented by its usual
stage representatives and eventual-equality criterion. These conditions concern
only rings; they contain no assertion about differentials. Both colimit rings
are arbitrary chosen models. The implementation also proves that this
presentation has the ring colimit universal property. -/
namespace Specs.AdvCommAlg.Differentials

universe ui ua ub uA uB

/-- The explicit representative description of a directed colimit of rings. -/
structure RingColimitPresentation {ι : Type ui} [Preorder ι]
    (R : ι → Type ua) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    (T : Type uA) [CommRing T] (ιR : ∀ i, R i →+* T) : Prop where
  cocone : ∀ i j h x, ιR j (f i j h x) = ιR i x
  representative : ∀ x : T, ∃ i y, ιR i y = x
  eventually_equal : ∀ i (x y : R i), ιR i x = ιR i y →
    ∃ (j : ι) (h : i ≤ j), f i j h x = f i j h y

open scoped TensorProduct

/-- Existence of the canonical transition system and the canonical comparison
isomorphism. Its formula includes every extended stage differential. Identity
and composition are asserted as equalities of linear maps. No finiteness,
flatness, injectivity of transitions, or nonzero-ring hypothesis is present. -/
noncomputable def directedColimits : Prop :=
  ∀ (ι : Type ui) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (Ai : ι → Type ua) (Bi : ι → Type ub)
    [∀ i, CommRing (Ai i)] [∀ i, CommRing (Bi i)] [∀ i, Algebra (Ai i) (Bi i)]
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B] [Algebra A B]
    [∀ i, Algebra (Ai i) A] [∀ i, Algebra (Bi i) B]
    (fa : ∀ i j, i ≤ j → Ai i →+* Ai j)
    (fb : ∀ i j, i ≤ j → Bi i →+* Bi j)
    [DirectedSystem Ai (fa · · ·)] [DirectedSystem Bi (fb · · ·)]
    (square : ∀ i j h, (fb i j h).comp (algebraMap (Ai i) (Bi i)) =
      (algebraMap (Ai j) (Bi j)).comp (fa i j h))
    (hA : RingColimitPresentation Ai fa A (fun i => algebraMap (Ai i) A))
    (hB : RingColimitPresentation Bi fb B (fun i => algebraMap (Bi i) B))
    (limitSquare : ∀ i, (algebraMap (Bi i) B).comp (algebraMap (Ai i) (Bi i)) =
      (algebraMap A B).comp (algebraMap (Ai i) A)),
  letI : DecidableEq ι := Classical.decEq ι
  ∃ t : ∀ i j, i ≤ j →
      (B ⊗[Bi i] KaehlerDifferential (Ai i) (Bi i)) →ₗ[B]
      (B ⊗[Bi j] KaehlerDifferential (Ai j) (Bi j)),
    (∀ i j h (c : B) (b : Bi i),
      t i j h (c ⊗ₜ[Bi i] KaehlerDifferential.D (Ai i) (Bi i) b) =
        c ⊗ₜ[Bi j] KaehlerDifferential.D (Ai j) (Bi j) (fb i j h b)) ∧
    (∀ i, t i i le_rfl = LinearMap.id) ∧
    (∀ i j k (h : i ≤ j) (h' : j ≤ k),
      (t j k h').comp (t i j h) = t i k (h.trans h')) ∧
    ∃ e : Module.DirectLimit (fun i => B ⊗[Bi i] KaehlerDifferential (Ai i) (Bi i)) t
        ≃ₗ[B] KaehlerDifferential A B,
      ∀ i (c : B) (b : Bi i),
        e (Module.DirectLimit.of B ι _ t i
          (c ⊗ₜ[Bi i] KaehlerDifferential.D (Ai i) (Bi i) b)) =
        c • KaehlerDifferential.D A B (algebraMap (Bi i) B b)

end Specs.AdvCommAlg.Differentials
