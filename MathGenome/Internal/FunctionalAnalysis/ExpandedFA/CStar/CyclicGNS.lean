import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.CyclicGNS
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.PositiveFunctionals
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
namespace ExpandedFA.CStar.CyclicGNS
universe u v w
open scoped InnerProductSpace ComplexOrder
open UniformSpace

section Ordered
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private def classMap (f : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] f.GNS :=
  (Completion.toComplL : f.PreGNS →L[ℂ] f.GNS).toLinearMap.comp f.toPreGNS.toLinearMap

private lemma classMap_inner (f : A →ₚ[ℂ] ℂ) (a b : A) :
    ⟪classMap f a, classMap f b⟫_ℂ = f (star a * b) := by
  change ⟪(f.toPreGNS a : f.GNS), (f.toPreGNS b : f.GNS)⟫_ℂ = _
  exact Completion.inner_coe _ _

private lemma classMap_dense (f : A →ₚ[ℂ] ℂ) : DenseRange (classMap f) := by
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

private lemma classMap_action (f : A →ₚ[ℂ] ℂ) (c a : A) :
    f.gnsStarAlgHom c (classMap f a) = classMap f (c * a) := by
  change f.gnsNonUnitalStarAlgHom c (f.toPreGNS a : f.GNS) = _
  simp only [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  rfl

end Ordered

theorem existence : Spec.Existence.{u} := by
  intro A _ φ
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let f := PositiveFunctionals.positiveMap φ.val φ.property.1
  let q := classMap f
  have hq : ∀ a b, ⟪q a, q b⟫_ℂ = φ.val (star a * b) := classMap_inner f
  have hker : PositiveFunctionals.nullSpace A φ.val = LinearMap.ker q := by
    change Submodule.span ℂ _ = _
    have hs : {a : A | φ.val (star a * a) = 0} = (LinearMap.ker q : Set A) := by
      ext a
      change φ.val (star a * a) = 0 ↔ q a = 0
      rw [← hq, inner_self_eq_zero]
    rw [hs, Submodule.span_eq]
  let N := PositiveFunctionals.nullSpace A φ.val
  let j : PositiveFunctionals.Spec.NullQuotient φ.val →ₗ[ℂ] f.GNS :=
    N.liftQ q hker.le
  have hj : ∀ a, j (Submodule.Quotient.mk a) = q a := fun _ => rfl
  have hjdense : DenseRange j := (classMap_dense f).mono (by
    rintro _ ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, rfl⟩)
  have hact : ∀ c a, f.gnsStarAlgHom c (q a) = q (c * a) := classMap_action f
  have hξ : ‖q 1‖ = 1 := by
    have hn : ‖q 1‖ ^ 2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), hq]
      simp [φ.property.2]
    nlinarith [norm_nonneg (q 1)]
  refine ⟨f.GNS, inferInstance, inferInstance, inferInstance, ⟨{
    π := f.gnsStarAlgHom
    ξ := q 1
    unit_vector := hξ
    cyclic := ?_
    coefficient := ?_
    j := j
    injective := LinearMap.ker_eq_bot.mp (N.ker_liftQ_eq_bot q hker.le hker.ge)
    dense := hjdense
    inner_classes := hq
    vector_class := rfl
    left_action := hact
    norm_bound := ?_
  }⟩⟩
  · have heq : (fun a => f.gnsStarAlgHom a (q 1)) = q := by
      funext a
      simpa using hact a 1
    rw [heq]
    exact classMap_dense f
  · intro a
    rw [hact, mul_one, hq]
    simp
  · exact fun a => NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a

section Uniqueness
variable {A : Type u} [CStarAlgebra A] {φ : Conventions.Spec.StateValue A}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def orbitMap (r : Spec.Realization (H := H) φ) : A →ₗ[ℂ] H where
  toFun a := r.π a r.ξ
  map_add' a b := by simp
  map_smul' z a := by simp

private lemma orbitMap_one (r : Spec.Realization (H := H) φ) : orbitMap r 1 = r.ξ := by
  simp [orbitMap]

private lemma orbitMap_mul (r : Spec.Realization (H := H) φ) (a b : A) :
    orbitMap r (a * b) = r.π a (orbitMap r b) := by
  simp [orbitMap]

private lemma orbitMap_inner (r : Spec.Realization (H := H) φ) (a b : A) :
    ⟪orbitMap r a, orbitMap r b⟫_ℂ = φ.val (star a * b) := by
  change ⟪r.π a r.ξ, r.π b r.ξ⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [r.coefficient, map_mul, map_star]
  rfl

end Uniqueness

/-- The unitary extends the isometric map between the two dense cyclic orbits.
Its intertwining identity and its uniqueness follow from that same density. -/
theorem uniqueness : Spec.Uniqueness.{u, v, w} := by
  intro A _ φ H K _ _ _ _ _ _ r s
  let e₁ := orbitMap r
  let e₂ := orbitMap s
  have hn : ∀ a, ‖e₂ a‖ = ‖e₁ a‖ := by
    intro a
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖orbitMap s a‖ ^ 2 = ‖orbitMap r a‖ ^ 2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      orbitMap_inner, orbitMap_inner]
  let U : H ≃ₗᵢ[ℂ] K := (LinearEquiv.refl ℂ A).extendOfIsometry
    e₁ e₂ r.cyclic s.cyclic hn
  have hU : ∀ a, U (e₁ a) = e₂ a := by
    intro a
    exact LinearEquiv.extendOfIsometry_eq _ _ _ r.cyclic s.cyclic hn a
  have hv : U r.ξ = s.ξ := by
    simpa only [e₁, e₂, orbitMap_one] using hU 1
  refine ⟨U, ⟨hv, ?_⟩, ?_⟩
  · intro a x
    apply congrFun (r.cyclic.equalizer
      ((U.continuous).comp (r.π a).continuous)
      ((s.π a).continuous.comp U.continuous) ?_) x
    funext b
    change U (r.π a (e₁ b)) = s.π a (U (e₁ b))
    calc
      _ = U (e₁ (a * b)) := by exact congrArg U (orbitMap_mul r a b).symm
      _ = e₂ (a * b) := hU _
      _ = s.π a (U (e₁ b)) := by rw [hU]; exact orbitMap_mul s a b
  · intro V hV
    apply LinearIsometryEquiv.ext
    apply congrFun (r.cyclic.equalizer V.continuous U.continuous ?_)
    funext a
    change V (r.π a r.ξ) = U (e₁ a)
    rw [hV.2, hV.1, hU]
    rfl

end ExpandedFA.CStar.CyclicGNS
