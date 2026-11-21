import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.TotalComplexConstruction

/-! Total complexes and the sign conventions of paper.tex 2377–2414. -/
namespace P103.Ch10.TotalComplexAssembly
open CategoryTheory CategoryTheory.Limits DirectSum
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v

abbrev Bicomplex := @P103.Specs.Ch10.TotalComplexAssembly.Bicomplex.{u,v}
abbrev ChainBicomplex := @P103.Specs.Ch10.TotalComplexAssembly.ChainBicomplex.{u,v}
abbrev CochainBicomplex := @P103.Specs.Ch10.TotalComplexAssembly.CochainBicomplex.{u,v}
abbrev SupportedQuadrant := @P103.Specs.Ch10.TotalComplexAssembly.SupportedQuadrant.{u,v}
abbrev ColumnsAcyclic := @P103.Specs.Ch10.TotalComplexAssembly.ColumnsAcyclic.{u,v}
abbrev RowsAcyclic := @P103.Specs.Ch10.TotalComplexAssembly.RowsAcyclic.{u,v}
abbrev quadrantDiagonal := P103.Specs.Ch10.TotalComplexAssembly.quadrantDiagonal
abbrev total := @P103.Specs.Ch10.TotalComplexAssembly.total.{u,v}
abbrev diagonalFamily := @P103.Specs.Ch10.TotalComplexAssembly.diagonalFamily.{u,v}
abbrev totalTermEquiv := @P103.Specs.Ch10.TotalComplexAssembly.totalTermEquiv.{u,v}
abbrev totalInclusion := @P103.Specs.Ch10.TotalComplexAssembly.totalInclusion.{u,v}
abbrev totalProjection := @P103.Specs.Ch10.TotalComplexAssembly.totalProjection.{u,v}
abbrev totalSupport := @P103.Specs.Ch10.TotalComplexAssembly.totalSupport.{u,v}
abbrev signedInterchange := @P103.Specs.Ch10.TotalComplexAssembly.signedInterchange.{u,v}
abbrev AnticommutingBicomplex :=
  P103.Specs.Ch10.TotalComplexAssembly.AnticommutingBicomplex.{u,v}
abbrev signedColumn := @P103.Specs.Ch10.TotalComplexAssembly.signedColumn.{u,v}
abbrev anticommutingToCommuting :=
  @P103.Specs.Ch10.TotalComplexAssembly.AnticommutingBicomplex.toCommuting.{u,v}
abbrev anticommutingTotal :=
  @P103.Specs.Ch10.TotalComplexAssembly.AnticommutingBicomplex.total.{u,v}

theorem quadrantDiagonal_finite (a b n : ℤ) : (quadrantDiagonal a b n).Finite := by
  apply ((Set.finite_Icc a (n - b)).prod (Set.finite_Icc b (n - a))).subset
  rintro ⟨p, q⟩ ⟨hp, hq, hn⟩
  change (a ≤ p ∧ p ≤ n - b) ∧ b ≤ q ∧ q ≤ n - a
  omega

variable {R : Type u} [Ring R] {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]

/-- This formula determines the total differential on all summands. -/
theorem totalInclusion_d (K : Bicomplex.{u,v} R c) (p q n m : ℤ) (h : p + q = n) :
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p (c.next p)).f q ≫ K.ιTotalOrZero c (c.next p) q m +
        c.ε p • ((K.X p).d q (c.next q) ≫ K.ιTotalOrZero c p (c.next q) m) := by
  change K.ιTotal c p q n h ≫ (K.D₁ c n m + K.D₂ c n m) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂]
  simp only [HomologicalComplex₂.d₁, HomologicalComplex₂.d₂]
  change (1 : ℤˣ) • _ + _ = _
  rw [one_smul]
  rfl

/-- The chain convention is exactly dh + (-1)^p dv, lowering total degree. -/
theorem chain_totalInclusion_d (K : ChainBicomplex.{u,v} R) (p q n m : ℤ)
    (h : p + q = n) :
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p (p - 1)).f q ≫ K.ιTotalOrZero (ComplexShape.down ℤ) (p - 1) q m +
      p.negOnePow • ((K.X p).d q (q - 1) ≫
        K.ιTotalOrZero (ComplexShape.down ℤ) p (q - 1) m) := by
  change K.ιTotal (ComplexShape.down ℤ) p q n h ≫
    (K.D₁ (ComplexShape.down ℤ) n m + K.D₂ (ComplexShape.down ℤ) n m) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq' (ComplexShape.down ℤ) (show (ComplexShape.down ℤ).Rel p (p - 1) from by
      change p - 1 + 1 = p; omega) q m,
    K.d₂_eq' (ComplexShape.down ℤ) p (show (ComplexShape.down ℤ).Rel q (q - 1) from by
      change q - 1 + 1 = q; omega) m]
  change (1 : ℤˣ) • _ + p.negOnePow • _ = _
  rw [one_smul]

/-- The cochain convention is the same sign, raising total degree. -/
theorem cochain_totalInclusion_d (K : CochainBicomplex.{u,v} R) (p q n m : ℤ)
    (h : p + q = n) :
    totalInclusion K p q n h ≫ (total K).d n m =
      (K.d p (p + 1)).f q ≫ K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q m +
      p.negOnePow • ((K.X p).d q (q + 1) ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) p (q + 1) m) := by
  change K.ιTotal (ComplexShape.up ℤ) p q n h ≫
    (K.D₁ (ComplexShape.up ℤ) n m + K.D₂ (ComplexShape.up ℤ) n m) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from by
      change p + 1 = p + 1; omega) q m,
    K.d₂_eq' (ComplexShape.up ℤ) p (show (ComplexShape.up ℤ).Rel q (q + 1) from by
      change q + 1 = q + 1; omega) m]
  change (1 : ℤˣ) • _ + p.negOnePow • _ = _
  rw [one_smul]

/-- The chosen total really has square-zero differential in every degree. -/
theorem total_squared (K : Bicomplex.{u,v} R c) (i j k : ℤ) :
    ((total K).d j k).hom.comp ((total K).d i j).hom = 0 :=
  Complexes.differential_squared (total K) i j k

/-- The equivalence with the direct sum sends each canonical inclusion to lof. -/
theorem totalTermEquiv_inclusion (K : Bicomplex.{u,v} R c) (p q n : ℤ)
    (h : p + q = n) (x : (K.X p).X q) :
    totalTermEquiv K n ((totalInclusion K p q n h).hom x) =
      DirectSum.lof R _ (fun i => diagonalFamily K n i) ⟨(p, q), h⟩ x := by
  exact DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (ModuleCat.ι_coprodIsoDirectSum_hom (diagonalFamily K n) ⟨(p, q), h⟩)) x

/-- Projection onto the summand from which an element was included. -/
@[reassoc (attr := simp)] theorem totalInclusion_projection_self (K : Bicomplex.{u,v} R c)
    (p q n : ℤ) (h : p + q = n) :
    totalInclusion K p q n h ≫ totalProjection K p q n h = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x
  change DirectSum.component R _ (fun i => diagonalFamily K n i) ⟨(p, q), h⟩
    (totalTermEquiv K n ((totalInclusion K p q n h).hom x)) = x
  rw [totalTermEquiv_inclusion, DirectSum.component.lof_self]

/-- Distinct summands have zero cross-coordinate projection. -/
@[reassoc] theorem totalInclusion_projection_ne (K : Bicomplex.{u,v} R c)
    (p q p' q' n : ℤ) (h : p + q = n) (h' : p' + q' = n)
    (hne : p ≠ p' ∨ q ≠ q') :
    totalInclusion K p q n h ≫ totalProjection K p' q' n h' = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change DirectSum.component R _ (fun i => diagonalFamily K n i) ⟨(p', q'), h'⟩
    (totalTermEquiv K n ((totalInclusion K p q n h).hom x)) = 0
  rw [totalTermEquiv_inclusion, DirectSum.component.of, dite_eq_right]
  intro he
  have he' := congrArg Subtype.val he
  exact hne.elim (fun hp => hp (congrArg Prod.fst he'))
    (fun hq => hq (congrArg Prod.snd he'))

/-- Coordinates determine an arbitrary total element. -/
theorem total_ext (K : Bicomplex.{u,v} R c) (n : ℤ) (x y : (total K).X n)
    (h : ∀ p q (hpq : p + q = n),
      (totalProjection K p q n hpq).hom x = (totalProjection K p q n hpq).hom y) :
    x = y := by
  apply (totalTermEquiv K n).injective
  apply DirectSum.ext_component R
  rintro ⟨⟨p, q⟩, hpq⟩
  exact h p q hpq

/-- Every total element is the finite sum of its included coordinates. -/
theorem total_reconstruction (K : Bicomplex.{u,v} R c) (n : ℤ) (x : (total K).X n) :
    ∑ i ∈ totalSupport K n x,
      (totalInclusion K i.val.1 i.val.2 n i.property).hom
        ((totalProjection K i.val.1 i.val.2 n i.property).hom x) = x := by
  classical
  apply (totalTermEquiv K n).injective
  simp only [map_sum, totalTermEquiv_inclusion]
  exact DirectSum.sum_support_of (totalTermEquiv K n x)

/-- The inclusions jointly determine maps out of the total term. -/
theorem total_hom_ext (K : Bicomplex.{u,v} R c) (n : ℤ) {M : ModuleCat.{v} R}
    {f g : (total K).X n ⟶ M}
    (h : ∀ p q (hpq : p + q = n),
      totalInclusion K p q n hpq ≫ f = totalInclusion K p q n hpq ≫ g) : f = g := by
  apply HomologicalComplex₂.total.hom_ext
  exact h

/-- Each chain target coordinate receives exactly the two adjacent source coordinates. -/
theorem chain_totalProjection_d (K : ChainBicomplex.{u,v} R) (p q n : ℤ)
    (h : p + q = n - 1) :
    (total K).d n (n - 1) ≫ totalProjection K p q (n - 1) h =
      totalProjection K (p + 1) q n (by omega) ≫ (K.d (p + 1) p).f q +
      p.negOnePow • (totalProjection K p (q + 1) n (by omega) ≫ (K.X p).d (q + 1) q) := by
  have normalizeH (i j k m : ℤ) (hk : i - 1 = k)
      (hi : i - 1 + j = m) (hk' : k + j = m) :
      (K.d i (i - 1)).f j ≫ totalInclusion K (i - 1) j m hi =
        (K.d i k).f j ≫ totalInclusion K k j m hk' := by
    subst k
    rfl
  have normalizeV (i j k m : ℤ) (hk : j - 1 = k)
      (hi : i + (j - 1) = m) (hk' : i + k = m) :
      (K.X i).d j (j - 1) ≫ totalInclusion K i (j - 1) m hi =
        (K.X i).d j k ≫ totalInclusion K i k m hk' := by
    subst k
    rfl
  apply total_hom_ext K n
  intro i j hij
  change i + j = n at hij
  change totalInclusion K i j n hij ≫ ((total K).d n (n - 1) ≫ _) = _
  rw [← Category.assoc, chain_totalInclusion_d]
  rw [K.ιTotalOrZero_eq (ComplexShape.down ℤ) (i - 1) j (n - 1) (by change i - 1 + j = n - 1; omega),
      K.ιTotalOrZero_eq (ComplexShape.down ℤ) i (j - 1) (n - 1) (by change i + (j - 1) = n - 1; omega)]
  change (((K.d i (i - 1)).f j ≫ totalInclusion K (i - 1) j (n - 1) _) +
    i.negOnePow • ((K.X i).d j (j - 1) ≫ totalInclusion K i (j - 1) (n - 1) _)) ≫ _ = _
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  by_cases hi : i = p + 1
  · have hj : j = q := by omega
    subst i j
    rw [totalInclusion_projection_ne K (p + 1) (q - 1) p q (n - 1) _ _ (Or.inl (by omega)),
      totalInclusion_projection_ne_assoc K (p + 1) q p (q + 1) n _ _ (Or.inl (by omega))]
    simp only [totalInclusion_projection_self_assoc, comp_zero, zero_comp,
      smul_zero, add_zero]
    rw [← Category.assoc, normalizeH (p + 1) q p (n - 1) (by omega) _ h,
      Category.assoc, totalInclusion_projection_self, Category.comp_id]
  · by_cases hi' : i = p
    · have hj : j = q + 1 := by omega
      subst i j
      rw [totalInclusion_projection_ne K (p - 1) (q + 1) p q (n - 1) _ _ (Or.inl (by omega)),
        totalInclusion_projection_ne_assoc K p (q + 1) (p + 1) q n _ _ (Or.inl (by omega))]
      simp only [totalInclusion_projection_self_assoc, comp_zero, zero_comp]
      rw [← Category.assoc, normalizeV p (q + 1) q (n - 1) (by omega) _ h,
        Category.assoc, totalInclusion_projection_self, Category.comp_id]
    · rw [totalInclusion_projection_ne K (i - 1) j p q (n - 1) _ _ (Or.inl (by omega)),
        totalInclusion_projection_ne K i (j - 1) p q (n - 1) _ _ (Or.inl hi'),
        totalInclusion_projection_ne_assoc K i j (p + 1) q n _ _ (Or.inl hi),
        totalInclusion_projection_ne_assoc K i j p (q + 1) n _ _ (Or.inl hi')]
      simp

/-- Each cochain target coordinate receives exactly the two adjacent source coordinates. -/
theorem cochain_totalProjection_d (K : CochainBicomplex.{u,v} R) (p q n : ℤ)
    (h : p + q = n + 1) :
    (total K).d n (n + 1) ≫ totalProjection K p q (n + 1) h =
      totalProjection K (p - 1) q n (by omega) ≫ (K.d (p - 1) p).f q +
      p.negOnePow • (totalProjection K p (q - 1) n (by omega) ≫ (K.X p).d (q - 1) q) := by
  have normalizeH (i j k m : ℤ) (hk : i + 1 = k)
      (hi : i + 1 + j = m) (hk' : k + j = m) :
      (K.d i (i + 1)).f j ≫ totalInclusion K (i + 1) j m hi =
        (K.d i k).f j ≫ totalInclusion K k j m hk' := by
    subst k
    rfl
  have normalizeV (i j k m : ℤ) (hk : j + 1 = k)
      (hi : i + (j + 1) = m) (hk' : i + k = m) :
      (K.X i).d j (j + 1) ≫ totalInclusion K i (j + 1) m hi =
        (K.X i).d j k ≫ totalInclusion K i k m hk' := by
    subst k
    rfl
  apply total_hom_ext K n
  intro i j hij
  change i + j = n at hij
  change totalInclusion K i j n hij ≫ ((total K).d n (n + 1) ≫ _) = _
  rw [← Category.assoc, cochain_totalInclusion_d]
  rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (i + 1) j (n + 1) (by change i + 1 + j = n + 1; omega),
      K.ιTotalOrZero_eq (ComplexShape.up ℤ) i (j + 1) (n + 1) (by change i + (j + 1) = n + 1; omega)]
  change (((K.d i (i + 1)).f j ≫ totalInclusion K (i + 1) j (n + 1) _) +
    i.negOnePow • ((K.X i).d j (j + 1) ≫ totalInclusion K i (j + 1) (n + 1) _)) ≫ _ = _
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  by_cases hi : i = p - 1
  · have hj : j = q := by omega
    subst i j
    rw [totalInclusion_projection_ne K (p - 1) (q + 1) p q (n + 1) _ _ (Or.inl (by omega)),
      totalInclusion_projection_ne_assoc K (p - 1) q p (q - 1) n _ _ (Or.inl (by omega))]
    simp only [totalInclusion_projection_self_assoc, comp_zero, zero_comp,
      smul_zero, add_zero]
    rw [← Category.assoc, normalizeH (p - 1) q p (n + 1) (by omega) _ h,
      Category.assoc, totalInclusion_projection_self, Category.comp_id]
  · by_cases hi' : i = p
    · have hj : j = q - 1 := by omega
      subst i j
      rw [totalInclusion_projection_ne K (p + 1) (q - 1) p q (n + 1) _ _ (Or.inl (by omega)),
        totalInclusion_projection_ne_assoc K p (q - 1) (p - 1) q n _ _ (Or.inl (by omega))]
      simp only [totalInclusion_projection_self_assoc, comp_zero, zero_comp]
      rw [← Category.assoc, normalizeV p (q - 1) q (n + 1) (by omega) _ h,
        Category.assoc, totalInclusion_projection_self, Category.comp_id]
    · rw [totalInclusion_projection_ne K (i + 1) j p q (n + 1) _ _ (Or.inl (by omega)),
        totalInclusion_projection_ne K i (j + 1) p q (n + 1) _ _ (Or.inl hi'),
        totalInclusion_projection_ne_assoc K i j (p - 1) q n _ _ (Or.inl hi),
        totalInclusion_projection_ne_assoc K i j p (q - 1) n _ _ (Or.inl hi')]
      simp

/-- Below the corner degree the entire total term vanishes. -/
theorem total_supportedBelow (K : Bicomplex.{u,v} R c) (a b : ℤ)
    (hs : SupportedQuadrant K a b) (n : ℤ) (hn : n < a + b) :
    Subsingleton ((total K).X n) := by
  have : ∀ i : {i : ℤ × ℤ // i.1 + i.2 = n}, Subsingleton (diagonalFamily K n i) := by
    rintro ⟨⟨p, q⟩, hpq⟩
    apply hs p q
    omega
  exact ⟨fun x y => (totalTermEquiv K n).injective (Subsingleton.elim _ _)⟩

/-- Signed interchange, with the exact (-1)^(pq) summand formula for chains. -/
theorem signedInterchange_chain (K : ChainBicomplex.{u,v} R) (p q n : ℤ)
    (h : q + p = n) :
    K.flip.ιTotal (ComplexShape.down ℤ) q p n h ≫
        (signedInterchange K).hom.f n =
      (p * q).negOnePow • K.ιTotal (ComplexShape.down ℤ) p q n (by change p + q = n; omega) := by
  exact K.ιTotal_totalFlipIso_f_hom (ComplexShape.down ℤ) p q n h

/-- The same signed interchange formula for cochains. -/
theorem signedInterchange_cochain (K : CochainBicomplex.{u,v} R) (p q n : ℤ)
    (h : q + p = n) :
    K.flip.ιTotal (ComplexShape.up ℤ) q p n h ≫
        (signedInterchange K).hom.f n =
      (p * q).negOnePow • K.ιTotal (ComplexShape.up ℤ) p q n (by change p + q = n; omega) := by
  exact K.ιTotal_totalFlipIso_f_hom (ComplexShape.up ℤ) p q n h

/-- For anticommuting input the two signs cancel, leaving dh+dv. -/
theorem anticommutingTotal_d (A : AnticommutingBicomplex.{u,v} R c)
    (p q n m : ℤ) (h : p + q = n) :
    totalInclusion (anticommutingToCommuting A) p q n h ≫
        (anticommutingTotal A).d n m =
      A.horizontal p (c.next p) q ≫
        (anticommutingToCommuting A).ιTotalOrZero c (c.next p) q m +
      (A.column p).d q (c.next q) ≫
        (anticommutingToCommuting A).ιTotalOrZero c p (c.next q) m := by
  change totalInclusion (anticommutingToCommuting A) p q n h ≫
    (total (anticommutingToCommuting A)).d n m = _
  rw [totalInclusion_d]
  change A.horizontal p (c.next p) q ≫
      (anticommutingToCommuting A).ιTotalOrZero c (c.next p) q m +
    c.ε p • ((c.ε p • (A.column p).d q (c.next q)) ≫
      (anticommutingToCommuting A).ιTotalOrZero c p (c.next q) m) = _
  rw [Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul]

omit [ComplexShape.TensorSigns c] in
/-- Transport acyclicity across a complex isomorphism using quotient homology. -/
theorem acyclic_of_iso {C D : HomologicalComplex (ModuleCat.{v} R) c}
    (e : C ≅ D) (hC : Complexes.Acyclic C) : Complexes.Acyclic D := by
  intro n
  have hid := congrArg (fun f => Complexes.homologyMap f n) e.inv_hom_id
  rw [Complexes.homologyMap_comp, Complexes.homologyMap_id] at hid
  have hi : ∀ x, Complexes.homologyMap e.hom n (Complexes.homologyMap e.inv n x) = x :=
    fun x => DFunLike.congr_fun hid x
  exact ⟨fun x y => (hi x).symm.trans
    ((congrArg (Complexes.homologyMap e.hom n) ((hC n).elim _ _)).trans (hi y))⟩

omit [ComplexShape.TensorSigns c] in
/-- A unit sign changes neither cycles nor boundaries. -/
theorem signedColumn_cycles (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ)
    (n : ℤ) : Complexes.cycles (signedColumn C s) n = Complexes.cycles C n := by
  ext x
  change ((s • C.d n (c.next n)).hom x = 0) ↔ (C.d n (c.next n)).hom x = 0
  change s • ((C.d n (c.next n)).hom x) = 0 ↔ _
  exact smul_eq_zero_iff_eq s

omit [ComplexShape.TensorSigns c] in
theorem signedColumn_boundaries (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ)
    (n : ℤ) : Complexes.boundaries (signedColumn C s) n = Complexes.boundaries C n := by
  ext x
  change (∃ y, (s • C.d (c.prev n) n).hom y = x) ↔
    ∃ y, (C.d (c.prev n) n).hom y = x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨s • y, ?_⟩
    change (C.d (c.prev n) n).hom ((s : ℤ) • y) = (s : ℤ) • _
    exact map_zsmul _ _ _
  · rintro ⟨y, rfl⟩
    refine ⟨s⁻¹ • y, ?_⟩
    change (s : ℤ) • ((C.d (c.prev n) n).hom ((↑s⁻¹ : ℤ) • y)) = _
    rw [map_zsmul]
    change s • (s⁻¹ • ((C.d (c.prev n) n).hom y)) = _
    exact smul_inv_smul s _

omit [ComplexShape.TensorSigns c] in
theorem signedColumn_acyclic_iff (C : HomologicalComplex (ModuleCat.{v} R) c) (s : ℤˣ) :
    Complexes.Acyclic (signedColumn C s) ↔ Complexes.Acyclic C := by
  rw [Complexes.acyclic_iff, Complexes.acyclic_iff]
  simp only [signedColumn_cycles, signedColumn_boundaries]

/-- The vertical sign twist preserves the original column acyclicity hypothesis. -/
theorem anticommuting_columns_acyclic_iff (A : AnticommutingBicomplex.{u,v} R c) :
    ColumnsAcyclic (anticommutingToCommuting A) ↔
      ∀ p, Complexes.Acyclic (A.column p) := by
  exact forall_congr' (fun p => signedColumn_acyclic_iff (A.column p) (c.ε p))

/-- The sign twist leaves the original horizontal rows unchanged. -/
theorem anticommuting_rows_acyclic_iff (A : AnticommutingBicomplex.{u,v} R c) :
    RowsAcyclic (anticommutingToCommuting A) ↔
      ∀ q, Complexes.Acyclic (A.row q) := Iff.rfl

end
end P103.Ch10.TotalComplexAssembly
