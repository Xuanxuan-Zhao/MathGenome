import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.AlgebraicCovering
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.PunctureCompletion

/-! Independent statements for paper.tex:3625–3641 (D12.21.04).
The pullback retains the literal algebraic curve point and its ordinary topology.
The two restriction homeomorphisms identify it with the finite-point and infinity
restrictions of that same curve. No regularity at the missing center is asserted.
-/
noncomputable section
open Set
open D12Complex.AlgebraicCovering D12Complex.Ch20.PuncturedDiskLoops
open D12Complex.Ch20.PunctureCompletion D12Complex.Surfaces

namespace D12Complex.CyclicParameters

abbrev CurveOver (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ) :=
  {x : Disk r × Curve P // g (x.1 : ℂ) = x.2.val.1}

def diskProjection (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (x : CurveOver P g r) : Disk r := x.val.1

def rootCoordinate (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (x : CurveOver P g r) : ℂ := x.val.2.val.2

abbrev FiniteRestriction (P : Polynomial (Polynomial ℂ)) (c : ℂ) (r : ℝ) :=
  {x : Curve P // 0 < ‖x.val.1 - c‖ ∧ ‖x.val.1 - c‖ < r}

abbrev InfinityRestriction (P : Polynomial (Polynomial ℂ)) (r : ℝ) :=
  {x : Curve P // 0 < ‖x.val.1⁻¹‖ ∧ ‖x.val.1⁻¹‖ < r}

end D12Complex.CyclicParameters

namespace Specs.D12Complex.Ch21.CyclicParameters
open _root_.D12Complex _root_.D12Complex.CyclicParameters

def CurveOver_type := Polynomial (Polynomial ℂ) → (ℂ → ℂ) → ℝ → Type
def CurveOver_value : CurveOver_type := fun P g r =>
  {x : Disk r × Curve P // g (x.1 : ℂ) = x.2.val.1}
def diskProjection_type := (P : Polynomial (Polynomial ℂ)) → (g : ℂ → ℂ) →
  (r : ℝ) → CurveOver P g r → Disk r
def diskProjection_value : diskProjection_type := fun _ _ _ x => x.val.1
def rootCoordinate_type := (P : Polynomial (Polynomial ℂ)) → (g : ℂ → ℂ) →
  (r : ℝ) → CurveOver P g r → ℂ
def rootCoordinate_value : rootCoordinate_type := fun _ _ _ x => x.val.2.val.2
def FiniteRestriction_type := Polynomial (Polynomial ℂ) → ℂ → ℝ → Type
def FiniteRestriction_value : FiniteRestriction_type := fun P c r =>
  {x : Curve P // 0 < ‖x.val.1 - c‖ ∧ ‖x.val.1 - c‖ < r}
def InfinityRestriction_type := Polynomial (Polynomial ℂ) → ℝ → Type
def InfinityRestriction_value : InfinityRestriction_type := fun P r =>
  {x : Curve P // 0 < ‖x.val.1⁻¹‖ ∧ ‖x.val.1⁻¹‖ < r}

/-- Cycle length is the cardinality of the actual fiber in that component.
The orbit equivalence uses the positive generator's actual lift permutation,
so length one is included. The complex structure of each component is fixed
by its base-coordinate charts, and both parameter directions are holomorphic.
The final equation retains the original polynomial and original curve point. -/
def cyclicModel (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (hr : 0 < r) : Prop :=
  let E := CurveOver P g r
  let p := diskProjection P g r
  let w := rootCoordinate P g r
  ∃ cov : IsCoveringMap p,
    Finite (ConnectedComponents E) ∧
    (∀ b : Disk r, ∃ e : RootGerm P (g (b : ℂ)) ≃ (p ⁻¹' {b}),
      ∀ a, w (e a) = a.val.value) ∧
    ∀ (b : Disk r) (γ : Path b b), HasWinding γ 1 →
      let length : ConnectedComponents E → ℕ := fun j =>
        Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j}
      (∀ x y : p ⁻¹' {b},
        ConnectedComponents.mk (x : E) = ConnectedComponents.mk (y : E) ↔
          ∃ k : ℤ, (cov.monodromyPerm b
            (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)) ^ k) x = y) ∧
      (∀ j, 0 < length j) ∧
      (∀ j : ConnectedComponents E,
        ∃ σ : Equiv.Perm {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j},
          (∀ x, (σ x).val = cov.monodromyPerm b
            (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)) x.val) ∧
          σ ^ length j = 1 ∧
          ∀ x, Function.Bijective (fun i : Fin (length j) => (σ ^ i.val) x)) ∧
      ∀ j : ConnectedComponents E,
        ∃ (hn : 0 < length j)
          (S : RiemannSurface {x : E // ConnectedComponents.mk x = j})
          (T : RiemannSurface (Disk (rootRadius r (length j))))
          (Φ : Disk (rootRadius r (length j)) ≃ₜ {x : E // ConnectedComponents.mk x = j})
          (W : ℂ → ℂ),
          (∀ e ∈ S.atlas, ∀ x ∈ e.val.source, e.val x = (p x : ℂ)) ∧
          ScalarHolomorphic S (fun x => w x) ∧
          (∀ e ∈ T.atlas, ∀ t ∈ e.val.source, e.val t = (t : ℂ)) ∧
          HolomorphicMap T S Φ ∧ HolomorphicMap S T Φ.symm ∧
          HolomorphicOn {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < rootRadius r (length j)} W ∧
          ∀ t : Disk (rootRadius r (length j)),
            p (Φ t) = powerMap hr hn t ∧
            (Φ t).val.val.2.val.1 = g ((t : ℂ) ^ length j) ∧
            W t = w (Φ t) ∧
            (fiber P (g ((t : ℂ) ^ length j))).eval (W t) = 0

/-- Lifted local monodromy is the original algebraic-cover monodromy
along the corresponding base path. Together with the value-preserving
root-germ equivalences, this fixes its interpretation as root continuation. -/
def monodromy_naturality_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (g : ℂ → ℂ) (r : ℝ)
    (hadm : ∀ u : Disk r, g (u : ℂ) ∈ baseSet P)
    (hg : Continuous (fun u : Disk r => g (u : ℂ)))
    (cov : IsCoveringMap (diskProjection P g r))
    (globalCov : IsCoveringMap (projection P))
    (a b : Disk r) (γ : Path a b) (x : diskProjection P g r ⁻¹' {a}),
    let x₀ : projection P ⁻¹' {(⟨g (a : ℂ), hadm a⟩ : Base P)} :=
      ⟨x.val.val.2, Subtype.ext (x.val.property.symm.trans
        (congrArg (fun u : Disk r => g (u : ℂ)) x.property))⟩
    (globalCov.monodromy (.mk (γ.map (hg.subtype_mk _))) x₀).val =
      (cov.monodromy (.mk γ) x).val.val.2

def cyclic_parameters_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∀ (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r),
      HolomorphicOn {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ < r} g →
      (∀ u : Disk r, g (u : ℂ) ∈ baseSet P) → cyclicModel P g r hr

def finite_parameters_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∀ c ∈ exceptionalSet P, ∀ (r : ℝ) (hr : 0 < r),
      (∀ z : ℂ, 0 < ‖z - c‖ → ‖z - c‖ < r → z ∉ exceptionalSet P) →
      cyclicModel P (fun u => c + u) r hr ∧
      ∃ H : CurveOver P (fun u => c + u) r ≃ₜ FiniteRestriction P c r,
        ∀ x, (H x).val = x.val.2

def infinity_parameters_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    ∀ (r : ℝ) (hr : 0 < r),
      (∀ u : Disk r, (u : ℂ)⁻¹ ∉ exceptionalSet P) →
      cyclicModel P (fun u => u⁻¹) r hr ∧
      ∃ H : CurveOver P (fun u => u⁻¹) r ≃ₜ InfinityRestriction P r,
        ∀ x, (H x).val = x.val.2

/-- Finite exceptional sets admit the neighborhoods used above. -/
def admissible_radii_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (d : ℕ),
    Irreducible P → P.natDegree = d → 0 < d →
    (∀ c : ℂ, ∃ r : ℝ, 0 < r ∧
      ∀ z : ℂ, 0 < ‖z - c‖ → ‖z - c‖ < r → z ∉ exceptionalSet P) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ u : Disk r, (u : ℂ)⁻¹ ∉ exceptionalSet P

end Specs.D12Complex.Ch21.CyclicParameters
