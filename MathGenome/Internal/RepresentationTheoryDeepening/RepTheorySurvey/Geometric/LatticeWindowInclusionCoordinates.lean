import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinates

namespace RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinates

open LatticeModelSpecs LatticeWindowInclusionCoordinateSpecs

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private abbrev windowProjection (r : ℕ) (a : ℤ) (m : ℕ) :
    (scalarLattice r a).val →ₗ[O] Window r a m :=
  @Submodule.mkQ O ((scalarLattice r a).val : Type) inferInstance inferInstance inferInstance
    (windowLower r a m)

private abbrev windowClass (r : ℕ) (a : ℤ) (m : ℕ) (x : Fin r → O) : Window r a m :=
  windowProjection r a m (shiftedCoordinates r a x)

private theorem windowClass_surjective (r : ℕ) (a : ℤ) (m : ℕ) :
    Function.Surjective (windowClass r a m) :=
  (@Submodule.mkQ_surjective O ((scalarLattice r a).val : Type)
    inferInstance inferInstance inferInstance (windowLower r a m)).comp
      (shiftedCoordinates r a).surjective

private theorem windowCoordinates_class (r : ℕ) (a : ℤ) (m : ℕ)
    (x : Fin r → O) (i : Fin r) (j : Fin m) :
    windowCoordinates r a m (windowClass r a m x) (i, j) = PowerSeries.coeff j.val (x i) := by
  change jetCoefficients m
    (jetReduction m ((shiftedCoordinates r a).symm (shiftedCoordinates r a x) i)) j = _
  rw [LinearEquiv.symm_apply_apply, jetCoefficients_reduce]

private theorem windowClass_mem {r : ℕ} {a : ℤ} {m : ℕ} (L : Lattice r)
    (hlo : (scalarLattice r (a + (m : ℤ))).val ≤ L.val) (x : Fin r → O) :
    windowClass r a m x ∈ latticeSubspace a m L ↔ shiftedInclusion r a x ∈ L.val := by
  let P := L.val.comap (scalarLattice r a).val.subtype
  let Q := windowLower r a m
  let q := windowProjection r a m
  have hle : Q ≤ P := fun _ hx ↦ hlo hx
  have hcomap : (P.map q).comap q = P :=
    (@Submodule.comap_map_mkQ O ((scalarLattice r a).val : Type)
      inferInstance inferInstance inferInstance Q P).trans (sup_eq_right.mpr hle)
  change shiftedCoordinates r a x ∈ (P.map q).comap q ↔ _
  rw [hcomap]
  rfl

/-- Split a family of coefficients at degree `p`. -/
private def splitCoefficients (r p q : ℕ) :
    (Fin r × Fin (p + q) → ℂ) ≃ₗ[ℂ] (Fin r × Fin p → ℂ) × (Fin r × Fin q → ℂ) :=
  let indices := (Equiv.prodSumDistrib (Fin r) (Fin p) (Fin q)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin r)) finSumFinEquiv)
  LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) indices.symm ≪≫ₗ
    LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ

private def splitWindow (r : ℕ) (b : ℤ) (α m β : ℕ) :
    Window r b (α + (m + β)) ≃ₗ[ℂ] Window r (b + (α : ℤ)) m ×
      ((Fin r × Fin β → ℂ) × (Fin r × Fin α → ℂ)) :=
  windowCoordinates r b (α + (m + β)) ≪≫ₗ
    splitCoefficients r α (m + β) ≪≫ₗ
    LinearEquiv.prodComm ℂ _ _ ≪≫ₗ
    (splitCoefficients r m β).prodCongr (LinearEquiv.refl ℂ _) ≪≫ₗ
    LinearEquiv.prodAssoc ℂ _ _ _ ≪≫ₗ
    (windowCoordinates r (b + (α : ℤ)) m).symm.prodCongr (LinearEquiv.refl ℂ _)

private theorem splitWindow_initial (r : ℕ) (b : ℤ) (α m β : ℕ)
    (x : Fin r → O) (i : Fin r) (j : Fin α) :
    (splitWindow r b α m β (windowClass r b (α + (m + β)) x)).2.2 (i, j) =
      PowerSeries.coeff j.val (x i) :=
  windowCoordinates_class r b (α + (m + β)) x i (j.castAdd (m + β))

private theorem splitWindow_middle (r : ℕ) (b : ℤ) (α m β : ℕ)
    (x : Fin r → O) (i : Fin r) (j : Fin m) :
    windowCoordinates r (b + (α : ℤ)) m
      (splitWindow r b α m β (windowClass r b (α + (m + β)) x)).1 (i, j) =
      PowerSeries.coeff (α + j.val) (x i) := by
  rw [show (splitWindow r b α m β (windowClass r b (α + (m + β)) x)).1 =
    (windowCoordinates r (b + (α : ℤ)) m).symm
      (fun z ↦ windowCoordinates r b (α + (m + β))
        (windowClass r b (α + (m + β)) x) (z.1, Fin.natAdd α (z.2.castAdd β))) from rfl,
    LinearEquiv.apply_symm_apply]
  exact windowCoordinates_class r b (α + (m + β)) x i (Fin.natAdd α (j.castAdd β))

/-- The first `α` coefficients vanish precisely for representatives divisible by `t ^ α`. -/
private theorem splitWindow_initial_eq_zero (r : ℕ) (b : ℤ) (α m β : ℕ)
    (x : Fin r → O) :
    (splitWindow r b α m β (windowClass r b (α + (m + β)) x)).2.2 = 0 ↔
      ∃ y : Fin r → O, x = t ^ α • y := by
  constructor
  · intro h
    have hdvd (i : Fin r) : t ^ α ∣ x i := by
      have hx : x i ∈ (truncCoefficients α).ker := by
        apply LinearMap.mem_ker.mpr
        funext j
        change PowerSeries.coeff j.val (x i) = 0
        exact (splitWindow_initial r b α m β x i j).symm.trans (congrFun h (i, j))
      rw [truncCoefficients_ker, Submodule.restrictScalars_mem, jetIdeal,
        Ideal.mem_span_singleton] at hx
      exact hx
    choose y hy using hdvd
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩
    funext z
    obtain ⟨i, j⟩ := z
    rw [splitWindow_initial]
    change PowerSeries.coeff j.val (t ^ α * y i) = 0
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (Nat.not_le_of_lt j.isLt)]

/-- Multiplication by `t ^ α` places the smaller quotient in the middle block. -/
private theorem splitWindow_middle_shift (r : ℕ) (b : ℤ) (α m β : ℕ)
    (y : Fin r → O) :
    (splitWindow r b α m β (windowClass r b (α + (m + β)) (t ^ α • y))).1 =
      windowClass r (b + (α : ℤ)) m y := by
  apply (windowCoordinates r (b + (α : ℤ)) m).injective
  funext z
  obtain ⟨i, j⟩ := z
  rw [splitWindow_middle, windowCoordinates_class]
  change PowerSeries.coeff (α + j.val) (t ^ α * y i) = PowerSeries.coeff j.val (y i)
  rw [Nat.add_comm α j.val, PowerSeries.coeff_X_pow_mul]

private theorem splitWindow_mem (r : ℕ) (b : ℤ) (α m β : ℕ) (L : Lattice r)
    (hlo : (scalarLattice r (b + (α : ℤ) + (m : ℤ))).val ≤ L.val)
    (hhi : L.val ≤ (scalarLattice r (b + (α : ℤ))).val)
    (w : Window r b (α + (m + β))) :
    w ∈ latticeSubspace b (α + (m + β)) L ↔
      (splitWindow r b α m β w).1 ∈ latticeSubspace (b + (α : ℤ)) m L ∧
        (splitWindow r b α m β w).2.2 = 0 := by
  have hlo' : (scalarLattice r (b + ((α + (m + β) : ℕ) : ℤ))).val ≤ L.val := by
    have h : b + ((α + (m + β) : ℕ) : ℤ) = b + (α : ℤ) + (m : ℤ) + (β : ℤ) := by
      push_cast
      omega
    rw [h]
    exact (scalarLattice_add_nat_le r (b + (α : ℤ) + (m : ℤ)) β).trans hlo
  obtain ⟨x, rfl⟩ := windowClass_surjective r b (α + (m + β)) w
  rw [windowClass_mem L hlo', splitWindow_initial_eq_zero]
  have hshift (y : Fin r → O) :
      shiftedInclusion r b (t ^ α • y) ∈ L.val ↔
        (splitWindow r b α m β (windowClass r b (α + (m + β)) (t ^ α • y))).1 ∈
          latticeSubspace (b + (α : ℤ)) m L := by
    rw [splitWindow_middle_shift, windowClass_mem L hlo, shiftedInclusion_add_nat]
  constructor
  · intro hx
    have hxupper := hhi hx
    rw [scalarLattice_val, LinearMap.mem_range] at hxupper
    obtain ⟨y, hy⟩ := hxupper
    have heq : x = t ^ α • y := (shiftedInclusion_injective r b)
      (hy.symm.trans (shiftedInclusion_add_nat r b α y))
    refine ⟨?_, ⟨y, heq⟩⟩
    rw [heq] at hx ⊢
    exact (hshift y).mp hx
  · rintro ⟨hy, y, rfl⟩
    exact (hshift y).mpr hy

theorem windowInclusionCoordinates : WindowInclusionCoordinates := by
  intro r a b m k hba hend
  dsimp only
  set α := (a - b).toNat
  set β := (b + (k : ℤ) - (a + (m : ℤ))).toNat
  have hα : (α : ℤ) = a - b := Int.toNat_of_nonneg (sub_nonneg.mpr hba)
  have hβ : (β : ℤ) = b + (k : ℤ) - (a + (m : ℤ)) :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hend)
  have ha : a = b + (α : ℤ) := by omega
  have hk : k = α + (m + β) := by omega
  clear_value α β
  subst a k
  refine ⟨splitWindow r b α m β, splitWindow_mem r b α m β, ?_, ?_⟩ <;>
    simp [Module.finrank_fintype_fun_eq_card]

end

end RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinates
