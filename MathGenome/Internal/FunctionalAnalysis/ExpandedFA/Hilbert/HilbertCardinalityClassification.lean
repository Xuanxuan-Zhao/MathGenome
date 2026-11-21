import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.HilbertCardinalityClassification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.OrthonormalExpansion
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
The cardinal invariant and classification, paper.tex 7465–7497.
For infinite bases, countable coefficient supports cover the other index
set; cardinal arithmetic bounds its cardinal by that of the infinite basis.
For a finite basis, totality makes it an algebraic basis, so finite-dimensional
linear algebra applies, also for the empty basis. A bijection of bases gives
coordinate isometries to the same ℓ² space and hence a unitary.
-/

noncomputable section
open scoped InnerProductSpace
open Cardinal

namespace ExpandedFA.Hilbert.HilbertCardinalityClassification
universe u v t w z

/-- Convert the shared maximal-family representation into Mathlib's complete
coordinate representation. No extra totality certificate is assumed. -/
def hilbertBasisOfMaximal {𝕜 : Type u} {H : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {e : ι → H} (he : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H ι e) :
    HilbertBasis ι 𝕜 H :=
  HilbertBasis.mk he.1 ((OrthonormalExpansion.maximal_iff_total 𝕜 H ι e he.1).mp he).ge

@[simp]
theorem coe_hilbertBasisOfMaximal {𝕜 : Type u} {H : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {e : ι → H} (he : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H ι e) :
    ⇑(hilbertBasisOfMaximal he) = e := HilbertBasis.coe_mk _ _

/-- The countable supports against a total family cover every orthonormal
vector, since such a vector cannot be orthogonal to the whole space. -/
theorem coefficient_supports_cover {𝕜 : Type u} {H : Type v}
    {ι : Type w} {κ : Type z} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {e : ι → H} {f : κ → H} (he : Orthonormal 𝕜 e)
    (hf : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H κ f) :
    (⋃ j, {i | ⟪e i, f j⟫_𝕜 ≠ 0}) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro i
  by_contra hi
  have hz : ∀ j, ⟪f j, e i⟫_𝕜 = 0 := by
    intro j
    apply inner_eq_zero_symm.mp
    by_contra h
    exact hi (Set.mem_iUnion.mpr ⟨j, h⟩)
  have hei : e i = 0 := by
    have hx := (OrthonormalExpansion.expansion 𝕜 H κ f hf (e i)).2
    simpa only [hz, zero_smul, tsum_zero] using hx
  have := he.norm_eq_one i
  rw [hei, norm_zero] at this
  exact zero_ne_one this

/-- An orthonormal family's cardinal is bounded by that of any infinite
orthonormal basis of the space. -/
theorem cardinal_le_of_infinite_basis {𝕜 : Type u} {H : Type v}
    {ι : Type w} {κ : Type z} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Infinite κ] {e : ι → H} {f : κ → H} (he : Orthonormal 𝕜 e)
    (hf : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H κ f) :
    Cardinal.lift.{z} #ι ≤ Cardinal.lift.{w} #κ := by
  have hb : (⨆ j, Cardinal.lift.{z} #({i | ⟪e i, f j⟫_𝕜 ≠ 0})) ≤ ℵ₀ := by
    apply ciSup_le'
    intro j
    have hc := OrthonormalExpansion.countable_coefficient_support 𝕜 H ι e he (f j)
    simpa using Cardinal.lift_le.{z, w}.mpr (Cardinal.le_aleph0_iff_set_countable.mpr hc)
  have h := Cardinal.mk_iUnion_le_lift (fun j => {i | ⟪e i, f j⟫_𝕜 ≠ 0})
  rw [coefficient_supports_cover he hf, Cardinal.mk_univ] at h
  calc
    Cardinal.lift.{z} #ι ≤ Cardinal.lift.{w} #κ *
        ⨆ j, Cardinal.lift.{z} #({i | ⟪e i, f j⟫_𝕜 ≠ 0}) := h
    _ ≤ Cardinal.lift.{w} #κ * ℵ₀ := mul_le_mul' le_rfl hb
    _ = Cardinal.lift.{w} #κ := Cardinal.mul_aleph0_eq
      (Cardinal.aleph0_le_lift.mpr (Cardinal.aleph0_le_mk κ))

/-- In the finite case a complete orthonormal basis is an ordinary algebraic
basis. This also handles the zero-dimensional case. -/
theorem basis_cardinality_invariant_finite {𝕜 : Type u} {H : Type v}
    {ι : Type w} {κ : Type z} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Finite κ] {e : ι → H} {f : κ → H}
    (he : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H ι e)
    (hf : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H κ f) :
    Cardinal.lift.{z} #ι = Cardinal.lift.{w} #κ := by
  let := Fintype.ofFinite κ
  let b := (hilbertBasisOfMaximal hf).toOrthonormalBasis.toBasis
  let : FiniteDimensional 𝕜 H := b.finiteDimensional_of_finite
  let : Finite ι := he.1.linearIndependent.finite
  let := Fintype.ofFinite ι
  exact Cardinal.lift_mk_eq'.mpr
    ⟨((hilbertBasisOfMaximal he).toOrthonormalBasis.toBasis).indexEquiv b⟩

theorem basis_cardinality_invariant : Spec.BasisCardinalityInvariant.{u, v, w, z} := by
  intro 𝕜 H ι κ _ _ _ _ e f he hf
  rcases finite_or_infinite κ with hκ | hκ
  · let := hκ
    exact basis_cardinality_invariant_finite he hf
  · let := hκ
    rcases finite_or_infinite ι with hι | hι
    · let := hι
      exact (basis_cardinality_invariant_finite hf he).symm
    · let := hι
      exact le_antisymm (cardinal_le_of_infinite_basis he.1 hf)
        (cardinal_le_of_infinite_basis hf.1 he)

theorem basis_bijection_extends : Spec.BasisBijectionExtends.{u, v, t, w, z} := by
  intro 𝕜 H K ι κ _ _ _ _ _ _ _ e f he hf p
  classical
  let b := hilbertBasisOfMaximal he
  have ho : Orthonormal 𝕜 (f ∘ p) := hf.1.comp p p.injective
  have hr : Set.range (f ∘ p) = Set.range f := p.surjective.range_comp f
  have ht : (Submodule.span 𝕜 (Set.range (f ∘ p))).topologicalClosure = ⊤ := by
    rw [hr]
    exact (OrthonormalExpansion.maximal_iff_total 𝕜 K κ f hf.1).mp hf
  let c := HilbertBasis.mk ho ht.ge
  refine ⟨b.repr.trans c.repr.symm, ?_⟩
  intro i
  have hb : b i = e i := congrFun (coe_hilbertBasisOfMaximal he) i
  have hc : c i = f (p i) := congrFun (HilbertBasis.coe_mk ho ht.ge) i
  change c.repr.symm (b.repr (e i)) = f (p i)
  rw [← hb, b.repr_self, c.repr_symm_single, hc]

/-- A unitary takes a maximal orthonormal family to a maximal one. -/
theorem unitary_maps_basis {𝕜 : Type u} {H : Type v} {K : Type t} {ι : Type w}
    [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    {e : ι → H} (he : OrthonormalExpansion.IsMaximalOrthonormal 𝕜 H ι e)
    (U : H ≃ₗᵢ[𝕜] K) :
    OrthonormalExpansion.IsMaximalOrthonormal 𝕜 K ι (U ∘ e) := by
  have ho := he.1.comp_linearIsometryEquiv U
  apply (OrthonormalExpansion.maximal_iff_total 𝕜 K ι (U ∘ e) ho).mpr
  let b := hilbertBasisOfMaximal he
  let c : HilbertBasis ι 𝕜 K := HilbertBasis.ofRepr (U.symm.trans b.repr)
  have hc : ⇑c = U ∘ e := by
    classical
    funext i
    change U (b.repr.symm (lp.single 2 i (1 : 𝕜))) = U (e i)
    rw [b.repr_symm_single]
    exact congrArg U (congrFun (coe_hilbertBasisOfMaximal he) i)
  rw [← hc]
  exact c.dense_span

theorem unitary_classification : Spec.UnitaryClassification.{u, v, t, w, z} := by
  intro 𝕜 H K ι κ _ _ _ _ _ _ _ e f he hf
  constructor
  · rintro ⟨U⟩
    exact basis_cardinality_invariant 𝕜 K ι κ (U ∘ e) f (unitary_maps_basis he U) hf
  · intro h
    obtain ⟨p⟩ := Cardinal.lift_mk_eq'.mp h
    obtain ⟨U, _⟩ := basis_bijection_extends 𝕜 H K ι κ e f he hf p
    exact ⟨U⟩

end ExpandedFA.Hilbert.HilbertCardinalityClassification
