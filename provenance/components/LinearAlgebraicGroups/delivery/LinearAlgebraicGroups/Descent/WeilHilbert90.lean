import Specs.LinearAlgebraicGroups.Descent.WeilHilbert90
import LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import LinearAlgebraicGroups.Descent.NonabelianCohomology
import LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Descent.WeilHilbert90

open NonabelianCohomology
open WeilRestriction (extendedUnits multiplicativeRestriction multiplicativeRestrictionUnits)

noncomputable section

universe u

section FiniteLevel

variable {k K E : Type u} [Field k] [Field K] [Field E] [Algebra k K] [Algebra k E]

private abbrev tensorAut (σ : Gal(K/k)) : (K ⊗[k] E) ≃ₐ[k] (K ⊗[k] E) :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : E ≃ₐ[k] E)

private theorem tensorAut_mul (σ τ : Gal(K/k)) (x : K ⊗[k] E) :
    tensorAut (σ * τ) x = tensorAut σ (tensorAut τ x) :=
  DFunLike.congr_fun
    (Algebra.TensorProduct.congr_trans τ σ (AlgEquiv.refl : E ≃ₐ[k] E) AlgEquiv.refl) x

private abbrev unitAction (σ : Gal(K/k)) : (K ⊗[k] E)ˣ →* (K ⊗[k] E)ˣ :=
  Units.map (tensorAut σ).toMonoidHom

private def twistedAction (a : Gal(K/k) → (K ⊗[k] E)ˣ)
    (ha : ∀ σ τ, a (σ * τ) = a σ * unitAction σ (a τ)) :
    SemilinearAction k K (K ⊗[k] E) where
  act σ := (tensorAut σ).toAddEquiv.trans (DistribMulAction.toAddEquiv _ (a σ))
  one_act x := by
    have hσ : tensorAut (1 : Gal(K/k)) = (AlgEquiv.refl : (K ⊗[k] E) ≃ₐ[k] _) :=
      Algebra.TensorProduct.congr_refl
    have hu (v : (K ⊗[k] E)ˣ) : unitAction (1 : Gal(K/k)) v = v :=
      Units.ext (DFunLike.congr_fun hσ (v : K ⊗[k] E))
    have h : a 1 = 1 := by
      simpa [hu] using ha 1 1
    change (a 1 : K ⊗[k] E) * tensorAut 1 x = x
    rw [h, hσ]
    exact one_mul x
  mul_act σ τ x := by
    change (a (σ * τ) : K ⊗[k] E) * tensorAut (σ * τ) x =
      (a σ : K ⊗[k] E) * tensorAut σ ((a τ : K ⊗[k] E) * tensorAut τ x)
    rw [ha, Units.val_mul, tensorAut_mul, map_mul]
    exact mul_assoc _ _ _
  map_smul σ r x := by
    change (a σ : K ⊗[k] E) * tensorAut σ (r • x) =
      σ r • ((a σ : K ⊗[k] E) * tensorAut σ x)
    simp only [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom]
    ac_rfl

private theorem finiteUnitCoboundary [Module.Finite k K] [IsGalois k K] [Module.Finite k E]
    (a : Gal(K/k) → (K ⊗[k] E)ˣ)
    (ha : ∀ σ τ, a (σ * τ) = a σ * unitAction σ (a τ)) :
    ∃ b : (K ⊗[k] E)ˣ, ∀ σ, a σ = b⁻¹ * unitAction σ b := by
  let T := K ⊗[k] E
  let ρ := twistedAction a ha
  have hdim := ρ.finiteDimensional_fixed
  let : Module.Finite k ρ.fixed := hdim.1
  have he : Module.finrank k ρ.fixed = Module.finrank k E :=
    hdim.2.trans Module.finrank_baseChange
  have : Nontrivial ρ.fixed := (Module.finrank_pos_iff_of_free k _).mp (by
    rw [he]
    exact Module.finrank_pos)
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.fixed)
  have hv' : (v : T) ≠ 0 := by
    exact fun hz => hv (Subtype.ext hz)
  -- Multiplication by a nonzero fixed vector embeds E in the fixed space.
  let m : T →ₗ[K] T := LinearMap.mulLeft K (v : T)
  let j : E →ₐ[k] T := Algebra.TensorProduct.includeRight
  let f : E →ₗ[k] ρ.fixed :=
    ((m.restrictScalars k).comp j.toLinearMap).codRestrict _ fun e σ => by
      change (a σ : T) * tensorAut σ ((v : T) * j e) = (v : T) * j e
      have hfixed : (a σ : T) * tensorAut σ (v : T) = (v : T) := v.property σ
      have hj : tensorAut σ (j e) = j e := by
        change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k E) (1 ⊗ₜ[k] e) =
          1 ⊗ₜ[k] e
        simp
      rw [map_mul, hj, ← mul_assoc, hfixed]
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun e hz => by
    by_contra hne
    have hu : IsUnit (j e) := (isUnit_iff_ne_zero.mpr hne).map j
    have hzero : (v : T) * j e = 0 := congrArg Subtype.val hz
    obtain ⟨z, hz'⟩ := isUnit_iff_exists_inv.mp hu
    apply hv'
    calc
      (v : T) = (v : T) * (j e * z) := by rw [hz', mul_one]
      _ = 0 := by rw [← mul_assoc, hzero, zero_mul]
  have hsurj : Function.Surjective f :=
    (LinearEquiv.ofInjectiveOfFinrankEq f hf he.symm).surjective
  -- The embedding is onto by dimension. The fixed vectors span the tensor algebra
  -- over K, so multiplication by v hits 1.
  have hspan : Submodule.span K (ρ.fixed : Set T) ≤ LinearMap.range m :=
    Submodule.span_le.mpr fun x hx => by
      obtain ⟨e, h⟩ := hsurj ⟨x, hx⟩
      exact ⟨j e, congrArg Subtype.val h⟩
  have htop : LinearMap.range m = ⊤ := by
    rwa [ρ.span_fixed_eq_top, top_le_iff] at hspan
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp htop (1 : T)
  let vUnit : Tˣ := (isUnit_iff_exists_inv.mpr ⟨y, hy⟩ : IsUnit (v : T)).unit
  have hval : (vUnit : T) = (v : T) := IsUnit.unit_spec _
  refine ⟨vUnit⁻¹, fun σ => ?_⟩
  rw [inv_inv, map_inv, eq_mul_inv_iff_mul_eq]
  apply Units.ext
  change (a σ : T) * tensorAut σ (vUnit : T) = (vUnit : T)
  rw [hval]
  exact v.property σ

end FiniteLevel

section GroupSchemes

variable {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
  {G : Specs.GroupScheme k}

private theorem groupH1_eq_basepoint_of_finite
    (solve : ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K] [IsGalois k K]
      (a : Gal(K/k) → NonabelianCohomology.Points k K G.X),
      (∀ σ τ, a (σ * τ) = a σ * pointAction k K G.X σ (a τ)) →
      ∃ b : NonabelianCohomology.Points k K G.X,
        ∀ σ, a σ = b⁻¹ * pointAction k K G.X σ b)
    (x : groupH1 k G.X S) : x = groupBasepoint k G.X S := by
  let : TopologicalSpace (NonabelianCohomology.Points k S G.X) := ⊥
  let : DiscreteTopology (NonabelianCohomology.Points k S G.X) := ⟨rfl⟩
  change x = basepoint (pointAction k S G.X)
  refine Quotient.inductionOn x fun a => ?_
  change classOf a = classOf (trivial _)
  obtain ⟨L, c, _, hc⟩ := finiteLevel (⊥ : FiniteGaloisIntermediateField k S) a
  obtain ⟨e, _, hequiv⟩ := finitePointsIdentification (H := G.X) L
  have hlaw (σ τ : Gal(L/k)) :
      e.symm (c (σ * τ)) = e.symm (c σ) * pointAction k L G.X σ (e.symm (c τ)) := by
    apply e.injective
    rw [e.apply_symm_apply, map_mul, e.apply_symm_apply, hequiv, e.apply_symm_apply]
    exact c.property.2 σ τ
  obtain ⟨b, hb⟩ := solve L (fun σ => e.symm (c σ)) hlaw
  apply classOf_eq_iff.mpr
  refine ⟨(e b).val⁻¹, fun σ => ?_⟩
  have h := congrArg Subtype.val (congrArg e (hb (restriction L σ)))
  rw [e.apply_symm_apply, map_mul, map_inv, hequiv] at h
  change (c (restriction L σ)).val = (e b).val⁻¹ *
    (levelAction (pointAction k S G.X) L (restriction L σ) (e b)).val at h
  rw [quotientAction_apply, hc σ] at h
  change (1 : NonabelianCohomology.Points k S G.X) =
    ((e b).val⁻¹)⁻¹ * a σ * pointAction k S G.X σ (e b).val⁻¹
  rw [h, map_inv]
  simp

private theorem finiteWeilCoboundary {E K : Type u} [Field E] [Algebra k E] [Module.Finite k E]
    [Field K] [Algebra k K] [Module.Finite k K] [IsGalois k K]
    (iso : (groupPointsFunctor k).obj G ≅ extendedUnits k E)
    (a : Gal(K/k) → NonabelianCohomology.Points k K G.X)
    (ha : ∀ σ τ, a (σ * τ) = a σ * pointAction k K G.X σ (a τ)) :
    ∃ b : NonabelianCohomology.Points k K G.X,
      ∀ σ, a σ = b⁻¹ * pointAction k K G.X σ b := by
  let e : NonabelianCohomology.Points k K G.X ≃* (K ⊗[k] E)ˣ :=
    (iso.app (CommAlgCat.of k K)).groupIsoToMulEquiv
  have hact (σ : Gal(K/k)) (p : NonabelianCohomology.Points k K G.X) :
      e (pointAction k K G.X σ p) = unitAction σ (e p) :=
    iso.hom.naturality_apply (CommAlgCat.ofHom σ.toAlgHom) p
  have hunit (σ τ : Gal(K/k)) : e (a (σ * τ)) = e (a σ) * unitAction σ (e (a τ)) := by
    rw [ha, map_mul, hact]
  obtain ⟨b, hb⟩ := finiteUnitCoboundary (fun σ => e (a σ)) hunit
  refine ⟨e.symm b, fun σ => e.injective ?_⟩
  rw [map_mul, map_inv, hact, e.apply_symm_apply, hb]

theorem vanishing : Specs.WeilHilbert90.Vanishing.{u} := by
  intro k E S _ _ _ _ _ _ _ _ W iso
  exact groupH1_eq_basepoint_of_finite (fun _ _ _ _ _ => finiteWeilCoboundary iso)

/-- Hilbert 90 for the canonical affine Weil restriction of the multiplicative group. -/
theorem multiplicativeRestriction_vanishing (k E S : Type u) [Field k] [Field E] [Field S]
    [Algebra k E] [Algebra k S] [Module.Finite k E] [Algebra.IsSeparable k E] [IsSepClosure k S]
    (x : groupH1 k (multiplicativeRestriction k E).val.X S) :
    x = groupBasepoint k (multiplicativeRestriction k E).val.X S :=
  vanishing k E S _ (multiplicativeRestrictionUnits k E) x

end GroupSchemes

/-- The class of any continuous cocycle of a finite product of Weil restrictions is neutral. -/
theorem product_vanishing : Specs.WeilHilbert90.ProductVanishing.{u} := by
  intro k S _ _ _ _ I _ E _ _ _ _ W iso P hP
  apply groupH1_eq_basepoint_of_finite
  intro K _ _ _ _ a ha
  let U := Grp.forget (SchemeOver k)
  have hQ := (Fan.isLimitMapConeEquiv U (fun i => (W i).val) P)
    (isLimitOfPreserves U hP)
  let π (i : I) : NonabelianCohomology.Points k K P.pt.X →*
      NonabelianCohomology.Points k K (W i).val.X := {
    toFun p := p ≫ (P.proj i).hom.hom
    map_one' := MonObj.one_comp (P.proj i).hom.hom
    map_mul' p q := MonObj.mul_comp p q (P.proj i).hom.hom }
  have hπ (i : I) (σ : Gal(K/k)) (p : NonabelianCohomology.Points k K P.pt.X) :
      π i (pointAction k K P.pt.X σ p) = pointAction k K (W i).val.X σ (π i p) := by
    let f := (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op
    change (f ≫ p) ≫ (P.proj i).hom.hom = f ≫ p ≫ (P.proj i).hom.hom
    exact Category.assoc _ _ _
  have hfactor (i : I) := finiteWeilCoboundary (iso i) (fun σ => π i (a σ)) (by
    intro σ τ
    rw [ha, map_mul, hπ])
  choose b hb using hfactor
  let w : NonabelianCohomology.Points k K P.pt.X := Fan.IsLimit.lift hQ b
  have hw (i : I) : π i w = b i := Fan.IsLimit.fac hQ b i
  refine ⟨w, fun σ => Fan.IsLimit.hom_ext hQ _ _ (fun i => ?_)⟩
  change π i (a σ) = π i (w⁻¹ * pointAction k K P.pt.X σ w)
  rw [map_mul, map_inv, hπ, hw, hb]

/-- Hilbert 90 for the categorical product of the canonical Weil restrictions. -/
theorem multiplicativeRestriction_product_vanishing
    (k S : Type u) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (I : Type u) [Finite I] (E : I → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra k (E i)] [∀ i, Module.Finite k (E i)]
    [∀ i, Algebra.IsSeparable k (E i)]
    (x : groupH1 k (∏ᶜ fun i => (multiplicativeRestriction k (E i)).val).X S) :
    x = groupBasepoint k (∏ᶜ fun i => (multiplicativeRestriction k (E i)).val).X S :=
  product_vanishing k S I E (fun i => multiplicativeRestriction k (E i))
    (fun i => multiplicativeRestrictionUnits k (E i)) _ (productIsProduct _) x

end

end LinearAlgebraicGroups.Descent.WeilHilbert90
