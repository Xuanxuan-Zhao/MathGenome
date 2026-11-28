import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionBundleBaseChange

namespace RepTheorySurvey.Geometric.ConvolutionBundleBaseChange

open ConvolutionBundleBaseChangeSpecs

/-- The incidence bounds and the image in the coefficient quotient are compatible
with taking spans along a semilinear coefficient map. -/
theorem affineBaseChange : AffineBaseChange := by
  intro R T A D _ _ _ _ _ _ a c S P hLower hUpper
  let S' := Submodule.span T (c '' (S : Set A))
  let generators := Prod.map c c '' (P : Set (A × A))
  let P' := Submodule.span T generators
  let U := S.prod (⊤ : Submodule R A)
  let U' := S'.prod (⊤ : Submodule T D)
  have coeff_mem {x : A} (hx : x ∈ S) : c x ∈ S' :=
    Submodule.subset_span ⟨x, hx, rfl⟩
  have upper : P' ≤ U' := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.mem_prod.mpr
      ⟨coeff_mem (Submodule.mem_prod.mp (hUpper hp)).1, Submodule.mem_top⟩
  have lower : (⊥ : Submodule T D).prod S' ≤ P' := by
    have h : S' ≤ P'.comap (LinearMap.inr T D D) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change (0, c x) ∈ P'
      apply Submodule.subset_span (s := generators)
      exact ⟨(0, x), hLower (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hx⟩), by simp⟩
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := Submodule.mem_prod.mp hxy
    have hx0 : x = 0 := (Submodule.mem_bot T).mp hx
    subst x
    exact h hy
  refine ⟨lower, upper, ?_⟩
  -- Restricting the span to the upper submodule keeps exactly the lifted generators.
  have restricted : P'.comap U'.subtype =
      Submodule.span T (U'.subtype ⁻¹' generators) := by
    have contained : generators ⊆ Set.range U'.subtype :=
      fun p hp ↦ ⟨⟨p, upper (Submodule.subset_span hp)⟩, rfl⟩
    apply Submodule.map_injective_of_injective U'.subtype_injective
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr upper, Submodule.map_span,
      Set.image_preimage_eq_of_subset contained]
  let B := (P.comap U.subtype).map (quotientCoefficients S)
  change (P'.comap U'.subtype).map (quotientCoefficients S') =
    Submodule.span T {z | ∃ (x : S) (y : A), (x, S.mkQ y) ∈ B ∧
      ∃ hx : c x.val ∈ S', z = (⟨c x.val, hx⟩, S'.mkQ (c y))}
  rw [restricted, Submodule.map_span]
  apply congrArg (Submodule.span T)
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨p, hp, he⟩ := hv
    have hp₁ := (Submodule.mem_prod.mp (hUpper hp)).1
    refine ⟨⟨p.1, hp₁⟩, p.2, ⟨⟨p, hUpper hp⟩, hp, rfl⟩, coeff_mem hp₁, ?_⟩
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he).symm)
      (congrArg S'.mkQ (congrArg Prod.snd he).symm)
  · rintro ⟨x, y, hxy, hx, rfl⟩
    obtain ⟨w, hw, he⟩ := hxy
    have hFirst : w.val.1 = x.val := congrArg (fun b : S × (A ⧸ S) ↦ b.1.val) he
    have hSecond : y - w.val.2 ∈ S :=
      (Submodule.Quotient.eq S).mp (congrArg Prod.snd he).symm
    -- Any representative of the quotient class differs by an element of the lower plane.
    have hDiff : (0, y - w.val.2) ∈ P :=
      hLower (Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hSecond⟩)
    have hSum : w.val + (0, y - w.val.2) = (x.val, y) :=
      Prod.ext (by change w.val.1 + 0 = x.val; rw [add_zero, hFirst])
        (by change w.val.2 + (y - w.val.2) = y; rw [add_comm, sub_add_cancel])
    have hp : (x.val, y) ∈ P :=
      hSum ▸ P.add_mem (show w.val ∈ P from hw) hDiff
    exact ⟨⟨(c x.val, c y), Submodule.mem_prod.mpr ⟨hx, Submodule.mem_top⟩⟩,
      ⟨(x.val, y), hp, rfl⟩, rfl⟩

end RepTheorySurvey.Geometric.ConvolutionBundleBaseChange
