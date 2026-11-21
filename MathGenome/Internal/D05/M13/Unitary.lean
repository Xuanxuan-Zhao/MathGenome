import MathGenome.Internal.Specs.D05.M13.Unitary
import MathGenome.Internal.D05.M03.EqualDimension
import MathGenome.Internal.D05.M12.Parallelogram
import MathGenome.Internal.D05.M13.AdjointLaws

/-! K05.13.unitary: inner-product isometries, unitaries, and orthogonal maps. -/

noncomputable section

namespace D05.M13.Unitary

/-- Inner-product preservation in the manuscript's convention. -/
def isometry {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W] (U : V →ₗ[F] W) : Prop :=
  D05.IsInnerIsometry U

/-- Surjective isometries, called unitary over ℂ and orthogonal over ℝ. -/
def unitary {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W] (U : V →ₗ[F] W) : Prop :=
  D05.IsUnitaryMap U

/-- The real specialization of the same surjective-isometry condition. -/
def orthogonal {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ V] [InnerProductSpace ℝ W] (U : V →ₗ[ℝ] W) : Prop :=
  D05.IsUnitaryMap U

theorem isometry_iff_linearIsometry :
    Specs.D05.M13.Unitary.isometry_iff_linearIsometry := by
  intro F V W _ _ _ _ _ U
  constructor
  · intro h
    exact ⟨U.isometryOfInner (fun x y => h y x), rfl⟩
  · rintro ⟨i, rfl⟩ x y
    exact i.inner_map_map y x

/-- Mathlib's norm characterization is proved by polarization, over both
real and complex scalars. Swapping the slots retains our shared convention. -/
theorem isometry_iff_norm : Specs.D05.M13.Unitary.isometry_iff_norm := by
  intro F V W _ _ _ _ _ U
  constructor
  · intro h
    exact (U.isometryOfInner (fun x y => h y x)).norm_map
  · intro h x y
    exact (LinearMap.norm_map_iff_inner_map_map U).mp h y x

theorem isometry_norm : Specs.D05.M13.Unitary.isometry_norm := by
  intro F V W _ _ _ _ _ U h
  exact (isometry_iff_norm U).mp h

theorem isometry_injective : Specs.D05.M13.Unitary.isometry_injective := by
  intro F V W _ _ _ _ _ U h
  exact (U.isometryOfInner (fun x y => h y x)).injective

/-- Test the equality of vectors against all inner products, and use the
adjoint identity. This does not assume surjectivity or equal dimensions. -/
theorem isometry_iff_adjoint_comp :
    Specs.D05.M13.Unitary.isometry_iff_adjoint_comp := by
  intro F V W _ _ _ _ _ _ _ U
  constructor
  · intro h
    ext y
    apply ext_inner_left F
    intro x
    change inner F x (LinearMap.adjoint U (U y)) = inner F x y
    rw [LinearMap.adjoint_inner_right]
    exact h y x
  · intro h x y
    change inner F (U y) (U x) = inner F y x
    rw [← LinearMap.adjoint_inner_right U y (U x)]
    change inner F y (((LinearMap.adjoint U).comp U) x) = inner F y x
    rw [h]
    rfl

/-- The left inverse becomes a right inverse by choosing a preimage in the
surjective case. The reverse implication gives preimages explicitly. -/
theorem unitary_iff_adjoint_identities :
    Specs.D05.M13.Unitary.unitary_iff_adjoint_identities := by
  intro F V W _ _ _ _ _ _ _ U
  constructor
  · rintro ⟨hi, hs⟩
    have hAU := (isometry_iff_adjoint_comp U).mp hi
    refine ⟨hAU, ?_⟩
    ext w
    obtain ⟨v, rfl⟩ := hs w
    exact congrArg U (DFunLike.congr_fun hAU v)
  · rintro ⟨hAU, hUA⟩
    refine ⟨(isometry_iff_adjoint_comp U).mpr hAU, ?_⟩
    intro w
    exact ⟨LinearMap.adjoint U w, DFunLike.congr_fun hUA w⟩

theorem unitary_bijective : Specs.D05.M13.Unitary.unitary_bijective := by
  intro F V W _ _ _ _ _ U h
  exact ⟨isometry_injective U h.1, h.2⟩

/-- Build the equivalence using the adjoint itself as the inverse function. -/
theorem unitary_inverse : Specs.D05.M13.Unitary.unitary_inverse := by
  intro F V W _ _ _ _ _ _ _ U h
  obtain ⟨hAU, hUA⟩ := (unitary_iff_adjoint_identities U).mp h
  let e : V ≃ₗ[F] W :=
    { U with
      invFun := LinearMap.adjoint U
      left_inv := fun v => DFunLike.congr_fun hAU v
      right_inv := fun w => DFunLike.congr_fun hUA w }
  exact ⟨e, rfl, rfl⟩

theorem inverse_eq_adjoint : Specs.D05.M13.Unitary.inverse_eq_adjoint := by
  intro F V W _ _ _ _ _ _ _ e h
  have hAU := (isometry_iff_adjoint_comp e.toLinearMap).mp h
  ext w
  obtain ⟨v, rfl⟩ := e.surjective w
  exact (e.symm_apply_apply v).trans (DFunLike.congr_fun hAU v).symm

theorem unitary_iff_linearIsometryEquiv :
    Specs.D05.M13.Unitary.unitary_iff_linearIsometryEquiv := by
  intro F V W _ _ _ _ _ U
  constructor
  · intro h
    let e : V ≃ₗ[F] W := LinearEquiv.ofBijective U (unitary_bijective U h)
    exact ⟨e.isometryOfInner (fun x y => h.1 y x), rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨fun x y => e.inner_map_map y x, e.surjective⟩

/-- The only dimension argument: an injective finite-dimensional endomorphism
is surjective by the proved equal-dimension theorem. -/
theorem endomorphism_isometry_iff_unitary :
    Specs.D05.M13.Unitary.endomorphism_isometry_iff_unitary := by
  intro F V _ _ _ _ U
  constructor
  · intro h
    exact ⟨h, (D05.M03.EqualDimension.equal_dimension U rfl).1.mp
      (isometry_injective U h)⟩
  · exact fun h => h.1

theorem endomorphism_adjoint_criterion :
    Specs.D05.M13.Unitary.endomorphism_adjoint_criterion := by
  intro F V _ _ _ _ U h
  have hu := (endomorphism_isometry_iff_unitary U).mp
    ((isometry_iff_adjoint_comp U).mpr h)
  exact ⟨((unitary_iff_adjoint_identities U).mp hu).2, unitary_inverse U hu⟩

/-- Explicit zero-space boundaries; the other theorems also quantify over
these spaces without an extra nonzero assumption. -/
theorem zero_map_isometry_iff : Specs.D05.M13.Unitary.zero_map_isometry_iff := by
  intro F V W _ _ _ _ _
  constructor
  · intro h
    have hn := isometry_norm (0 : V →ₗ[F] W) h
    have hz (x : V) : x = 0 := by
      apply norm_eq_zero.mp
      exact (hn x).symm.trans (norm_zero)
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · intro h
    letI := h
    intro x y
    have hx : x = 0 := Subsingleton.elim _ _
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hx, hy, D05.firstInner]

theorem zero_map_unitary_iff : Specs.D05.M13.Unitary.zero_map_unitary_iff := by
  intro F V W _ _ _ _ _
  constructor
  · intro h
    refine ⟨zero_map_isometry_iff.mp h.1, ?_⟩
    have hz (w : W) : w = 0 := by
      obtain ⟨v, hv⟩ := h.2 w
      exact hv.symm
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · rintro ⟨hV, hW⟩
    refine ⟨zero_map_isometry_iff.mpr hV, ?_⟩
    intro w
    exact ⟨0, Subsingleton.elim (α := W) _ _⟩

end D05.M13.Unitary
