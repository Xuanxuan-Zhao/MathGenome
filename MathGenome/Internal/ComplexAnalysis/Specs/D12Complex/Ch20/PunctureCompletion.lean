import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.PuncturedDiskLoops
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Homotopy.Lifting

/-! Independent interfaces for d12:20-08: the power model, connected
biholomorphic classification, and connected and disconnected completion.
-/
noncomputable section

namespace D12Complex.Ch20.PunctureCompletion
open PuncturedDiskLoops

/-- The positive real parameter radius in the source statement. -/
def rootRadius (r : ℝ) (m : ℕ) : ℝ := r ^ (1 / (m : ℝ))

/-- The norm bound that makes the power projection well typed. -/
lemma power_norm_bound {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m)
    {t : ℂ} (ht : ‖t‖ < rootRadius r m) : ‖t ^ m‖ < r := by
  rw [norm_pow]
  have hp : (rootRadius r m) ^ m = r := by
    simpa [rootRadius, one_div] using Real.rpow_inv_natCast_pow hr.le hm.ne'
  rw [← hp]
  exact pow_lt_pow_left₀ ht (norm_nonneg _) hm.ne'

/-- The actual punctured-disk power projection, not a fiber certificate. -/
def powerMap {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m)
    (t : Disk (rootRadius r m)) : Disk r :=
  ⟨(t : ℂ) ^ m, norm_pos_iff.mpr (pow_ne_zero m (norm_pos_iff.mp t.property.1)),
    power_norm_bound hr hm t.property.2⟩

end D12Complex.Ch20.PunctureCompletion

namespace Specs.D12Complex.Ch20.PunctureCompletion
open _root_.D12Complex.Ch20
open _root_.D12Complex.Ch20.PuncturedDiskLoops
open _root_.D12Complex.Ch20.PunctureCompletion

def rootRadius_type := ℝ → ℕ → ℝ
def rootRadius_value : rootRadius_type := fun r m => r ^ (1 / (m : ℝ))

def powerMap_type := {r : ℝ} → (hr : 0 < r) → {m : ℕ} → (hm : 0 < m) →
  Disk (rootRadius r m) → Disk r
def powerMap_value : powerMap_type := fun {_} hr {m} hm t =>
  ⟨(t : ℂ) ^ m, norm_pos_iff.mpr (pow_ne_zero m (norm_pos_iff.mp t.property.1)),
    power_norm_bound hr hm t.property.2⟩

def rootRadius_pos_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ m : ℕ, 0 < rootRadius r m

def rootRadius_pow_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {m : ℕ}, 0 < m → (rootRadius r m) ^ m = r

def norm_lt_rootRadius_iff_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {m : ℕ}, 0 < m → ∀ t : ℂ,
    (‖t‖ < rootRadius r m ↔ ‖t ^ m‖ < r)

def power_model_covering_type : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m), IsCovering (powerMap hr hm)

def power_model_fiber_card_type : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) (b : Disk r),
    Nat.card {t : Disk (rootRadius r m) // powerMap hr hm t = b} = m

def power_model_winding_type : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m)
    (b : Disk (rootRadius r m)) (γ : Path b b) (k : ℤ),
    HasWinding γ k → HasWinding (γ.map
      ((continuous_subtype_val.pow m).subtype_mk _ : Continuous (powerMap hr hm)))
      ((m : ℤ) * k)

/-- A continuous morphism of connected covers of the same positive finite
degree is a homeomorphism. Existence of such a morphism is a separate obligation. -/
def equal_degree_lift_homeomorphism_type : Prop :=
  ∀ {A E B : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace A] [PathConnectedSpace E]
    (q : A → B) (p : E → B), IsCovering q → IsCovering p →
    ∀ (m : ℕ), 0 < m →
    (∀ b, Nat.card (q ⁻¹' {b}) = m) → (∀ b, Nat.card (p ⁻¹' {b}) = m) →
    ∀ (f : A → E), Continuous f → p ∘ f = q → ∃ h : A ≃ₜ E, (h : A → E) = f

/-- The complete topological part of the connected classification, with an
arbitrary prescribed pair of initial points. Holomorphy is still to be proved. -/
def topological_classification_type : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) {E : Type*} [TopologicalSpace E]
    (_S : _root_.D12Complex.Surfaces.RiemannSurface E) (p : E → Disk r),
    IsCovering p → ∀ {m : ℕ} (hm : 0 < m),
    (∀ b, Nat.card (p ⁻¹' {b}) = m) →
    ∀ (b : Disk (rootRadius r m)) (e₀ : E), p e₀ = powerMap hr hm b →
    ∃ h : Disk (rootRadius r m) ≃ₜ E, h b = e₀ ∧ p ∘ h = powerMap hr hm

/-- The full connected analytic conclusion. The parameter surface has
the ordinary plane complex structure, specified by identity coordinate charts.
Both holomorphic directions are required. -/
def connected_classification_type : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) {E : Type*} [TopologicalSpace E]
    (S : _root_.D12Complex.Surfaces.RiemannSurface E) (p : E → Disk r),
    IsCovering p → _root_.D12Complex.Surfaces.ScalarHolomorphic S (fun x => (p x : ℂ)) →
    ∀ {m : ℕ} (hm : 0 < m), (∀ b, Nat.card (p ⁻¹' {b}) = m) →
    ∃ (T : _root_.D12Complex.Surfaces.RiemannSurface (Disk (rootRadius r m)))
      (Φ : Disk (rootRadius r m) ≃ₜ E),
      (∀ e ∈ T.atlas, ∀ t ∈ e.val.source, e.val t = (t : ℂ)) ∧
      _root_.D12Complex.Surfaces.HolomorphicMap T S Φ ∧
      _root_.D12Complex.Surfaces.HolomorphicMap S T Φ.symm ∧
      p ∘ Φ = powerMap hr hm

/-- The connected one-point extension. `Option E` fixes the underlying
set to exactly the old points and one new point, while its topology is an
output. The global coordinate identifies it with the full parameter disk.
-/
def connected_completion_type : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) {E : Type*} [TopologicalSpace E]
    (S : _root_.D12Complex.Surfaces.RiemannSurface E) (p : E → Disk r),
    IsCovering p → _root_.D12Complex.Surfaces.ScalarHolomorphic S (fun x => (p x : ℂ)) →
    ∀ {m : ℕ} (_hm : 0 < m), (∀ b, Nat.card (p ⁻¹' {b}) = m) →
    ∃ top : TopologicalSpace (Option E),
      letI := top
      let P : Option E → ℂ := fun x => match x with
        | none => 0
        | some e => (p e : ℂ)
      ∃ (C : _root_.D12Complex.Surfaces.RiemannSurface (Option E))
        (T : _root_.D12Complex.Surfaces.RiemannSurface ℂ)
        (c : _root_.D12Complex.Surfaces.ComplexChart (Option E)),
        (∀ e ∈ T.atlas, Set.EqOn e.val id e.val.source) ∧
        Topology.IsOpenEmbedding (some : E → Option E) ∧
        _root_.D12Complex.Surfaces.HolomorphicMap S C some ∧
        (∀ e : E, _root_.D12Complex.Surfaces.LocallyBiholomorphicAt S C some e) ∧
        c ∈ _root_.D12Complex.Surfaces.maximalAtlas C.atlas ∧
        c.val.source = Set.univ ∧ c.val.target = Metric.ball 0 (rootRadius r m) ∧
        c.val none = 0 ∧ (∀ x, P x = (c.val x) ^ m) ∧
        (∀ x, ‖P x‖ < r) ∧
        _root_.D12Complex.Surfaces.ScalarHolomorphic C P ∧
        _root_.D12Complex.Surfaces.HasMultiplicity C T P none m

/-- On any covering of the punctured disk, path reachability within a fiber
is exactly the orbit relation of the positive monodromy generator. -/
def joined_iff_monodromy_orbit_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {E : Type*} [TopologicalSpace E]
    {p : E → Disk r} (cov : IsCoveringMap p) (b : Disk r) (γ : Path b b), HasWinding γ 1 →
    ∀ x y : p ⁻¹' {b}, Joined (x : E) (y : E) ↔
      ∃ k : ℤ, (cov.monodromyPerm b (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)) ^ k) x = y

/-- Every component of a covering meets every base fiber. -/
def fiber_meets_components_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {E : Type*} [TopologicalSpace E]
    {p : E → Disk r} (cov : IsCoveringMap p) (b : Disk r) (e : E),
    ∃ x : p ⁻¹' {b}, Joined e (x : E)

/-- A finite fiber bounds the number of connected components, including
an empty total space. -/
def finite_components_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {E : Type*} [TopologicalSpace E]
    {p : E → Disk r} (cov : IsCoveringMap p) (b : Disk r),
    Finite (p ⁻¹' {b}) → Finite (ConnectedComponents E)

/-- The components are exactly the positive finite monodromy cycles.
No connectedness is imposed on the total atlas. -/
def monodromy_components_type : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {E : Type*} [TopologicalSpace E]
    (A : Set (_root_.D12Complex.Surfaces.ComplexChart E)),
    _root_.D12Complex.Surfaces.IsAtlas A → ∀ {p : E → Disk r}
      (cov : IsCoveringMap p) (b : Disk r) (γ : Path b b), HasWinding γ 1 →
      Finite (p ⁻¹' {b}) →
      Finite (ConnectedComponents E) ∧
      (∀ x y : p ⁻¹' {b},
        ConnectedComponents.mk (x : E) = ConnectedComponents.mk (y : E) ↔
          ∃ k : ℤ, (cov.monodromyPerm b
            (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)) ^ k) x = y) ∧
      ∀ j : ConnectedComponents E,
        0 < Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j}

/-- Full disconnected conclusion. The input is a Hausdorff,
second-countable complex atlas with no connectedness or nonemptiness imposed.
The underlying extension adds exactly one point per connected component;
the orbit equivalence identifies these with the actual monodromy cycles.
Their lengths include singleton cycles. The charts cover entire completed
components and preserve the original complex structure via local inverse pairs.
Multiplicity is tested in every compatible source and target chart, exactly
as in the canonical surface definition. -/
def disconnected_completion_type : Prop :=
  ∀ {r : ℝ} (hr : 0 < r) {E : Type*} [TopologicalSpace E]
    [T2Space E] [SecondCountableTopology E]
    (A : Set (_root_.D12Complex.Surfaces.ComplexChart E)),
    _root_.D12Complex.Surfaces.IsAtlas A → ∀ (p : E → Disk r),
    IsCovering p →
    (Continuous (fun x => (p x : ℂ)) ∧
      ∀ e ∈ A, _root_.D12Complex.HolomorphicOn e.val.target
        (fun z => (p (e.val.symm z) : ℂ))) →
    (∀ b, Finite (p ⁻¹' {b})) → ∀ (b : Disk r) (cov : IsCoveringMap p) (γ : Path b b), HasWinding γ 1 →
    let length : ConnectedComponents E → ℕ := fun j =>
      Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j}
    Finite (ConnectedComponents E) ∧
    (∀ x y : p ⁻¹' {b},
      ConnectedComponents.mk (x : E) = ConnectedComponents.mk (y : E) ↔
        ∃ k : ℤ, (cov.monodromyPerm b (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ)) ^ k) x = y) ∧
    (∀ j, 0 < length j) ∧
    ∃ top : TopologicalSpace (E ⊕ ConnectedComponents E),
      letI := top
      let P : E ⊕ ConnectedComponents E → ℂ := fun x => match x with
        | Sum.inl e => (p e : ℂ)
        | Sum.inr _ => 0
      T2Space (E ⊕ ConnectedComponents E) ∧
      SecondCountableTopology (E ⊕ ConnectedComponents E) ∧
      ∃ (B : Set (_root_.D12Complex.Surfaces.ComplexChart (E ⊕ ConnectedComponents E)))
        (T : _root_.D12Complex.Surfaces.RiemannSurface ℂ),
        _root_.D12Complex.Surfaces.IsAtlas B ∧
        (∀ e ∈ T.atlas, Set.EqOn e.val id e.val.source) ∧
        Topology.IsOpenEmbedding (Sum.inl : E → E ⊕ ConnectedComponents E) ∧
        (∀ a : E, ∃ e ∈ A, ∃ d ∈ B,
          a ∈ e.val.source ∧ Sum.inl a ∈ d.val.source ∧
          ∃ (U V : Set ℂ) (g : ℂ → ℂ), e.val a ∈ U ∧
            U ⊆ _root_.D12Complex.Surfaces.coordinateDomain e d Sum.inl ∧
            V ⊆ d.val.target ∧
            _root_.D12Complex.BiholomorphicPair U V
              (_root_.D12Complex.Surfaces.coordinateMap e d Sum.inl) g) ∧
        Continuous P ∧
        (∀ e ∈ B, _root_.D12Complex.HolomorphicOn e.val.target (P ∘ e.val.symm)) ∧
        (∀ x, ‖P x‖ < r) ∧
        ∀ j : ConnectedComponents E,
          ∃ c ∈ _root_.D12Complex.Surfaces.maximalAtlas B,
            c.val.source =
              (Sum.inl '' {e : E | ConnectedComponents.mk e = j}) ∪ {Sum.inr j} ∧
            c.val.target = Metric.ball 0 (rootRadius r (length j)) ∧
            c.val (Sum.inr j) = 0 ∧
            (∀ x ∈ c.val.source, P x = (c.val x) ^ length j) ∧
            ∀ e ∈ _root_.D12Complex.Surfaces.maximalAtlas B,
              ∀ d ∈ _root_.D12Complex.Surfaces.maximalAtlas T.atlas,
                Sum.inr j ∈ e.val.source → 0 ∈ d.val.source →
                  _root_.D12Complex.Surfaces.coordinateOrder e d P (Sum.inr j) =
                    (length j : ℕ∞)

end Specs.D12Complex.Ch20.PunctureCompletion
