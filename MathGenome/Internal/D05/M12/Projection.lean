import MathGenome.Internal.Specs.D05.M12.Projection
import MathGenome.Internal.D05.M12.FourierParseval
import MathGenome.Internal.D05.M12.OrthogonalDecomposition

/-! K05.12.projection: orthogonal projection onto a finite-dimensional
subspace of an arbitrary real or complex inner-product space. -/

noncomputable section

namespace D05.M12.Projection

abbrev projection : Specs.D05.M12.Projection.projection_type :=
  @_root_.D05.orthogonalProjection

theorem component_characterization : Specs.D05.M12.Projection.component_characterization := by
  intro F V _ _ _ U _ v u
  letI : CompleteSpace U := FiniteDimensional.complete F U
  change U.starProjection v = u ↔ u ∈ U ∧ v - u ∈ U.orthogonal
  constructor
  · rintro rfl
    exact ⟨U.starProjection_apply_mem v, Submodule.sub_starProjection_mem_orthogonal v⟩
  · rintro ⟨hu, hw⟩
    exact Submodule.eq_starProjection_of_mem_orthogonal hu hw

theorem unique_components : Specs.D05.M12.Projection.unique_components := by
  intro F V _ _ _ U _ v
  obtain ⟨p, hp, huniq⟩ := OrthogonalDecomposition.exists_unique_components U v
  have hproj : D05.orthogonalProjection U v = (p.1 : V) := by
    apply (component_characterization U v _).mpr
    refine ⟨p.1.property, ?_⟩
    have hv : v - (p.1 : V) = (p.2 : V) := by rw [← hp]; abel
    rw [hv]
    exact p.2.property
  exact ⟨p, ⟨hp, hproj⟩, fun q hq => huniq q hq.1⟩

theorem basis_formula : Specs.D05.M12.Projection.basis_formula := by
  intro F V I _ _ _ _ U _ b hb v
  letI : CompleteSpace U := FiniteDimensional.complete F U
  have h := FourierParseval.fourier_expansion b hb (U.orthogonalProjectionOnto v)
  have hc := congrArg (fun u : U => (u : V)) h
  simpa only [D05.orthogonalProjection, ContinuousLinearMap.coe_coe,
    Submodule.starProjection_apply, Submodule.coe_sum, Submodule.coe_smul,
    D05.firstInner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using hc

theorem basis_independence : Specs.D05.M12.Projection.basis_independence := by
  intro F V I J _ _ _ _ _ U _ b c hb hc v
  exact (basis_formula U b hb v).symm.trans (basis_formula U c hc v)

theorem map_add : Specs.D05.M12.Projection.map_add := by
  intro F V _ _ _ U _ x y
  exact (D05.orthogonalProjection U).map_add x y

theorem map_smul : Specs.D05.M12.Projection.map_smul := by
  intro F V _ _ _ U _ a v
  exact (D05.orthogonalProjection U).map_smul a v

theorem fixes_subspace : Specs.D05.M12.Projection.fixes_subspace := by
  intro F V _ _ _ U _ u hu
  apply (component_characterization U u u).mpr
  exact ⟨hu, by simp⟩

theorem idempotent : Specs.D05.M12.Projection.idempotent := by
  intro F V _ _ _ U _
  ext v
  apply fixes_subspace U
  exact ((component_characterization U v _).mp rfl).1

theorem range_eq : Specs.D05.M12.Projection.range_eq := by
  intro F V _ _ _ U _
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ((component_characterization U x _).mp rfl).1
  · intro hv
    exact ⟨v, fixes_subspace U v hv⟩

theorem kernel_eq : Specs.D05.M12.Projection.kernel_eq := by
  intro F V _ _ _ U _
  ext v
  change D05.orthogonalProjection U v = 0 ↔ v ∈ U.orthogonal
  rw [component_characterization]
  simp

theorem self_adjoint_identity : Specs.D05.M12.Projection.self_adjoint_identity := by
  intro F V _ _ _ U _ x y
  letI : CompleteSpace U := FiniteDimensional.complete F U
  change inner F y (U.starProjection x) = inner F (U.starProjection y) x
  exact (U.inner_starProjection_left_eq_right y x).symm

end D05.M12.Projection
