import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleTotalization
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FilteredComplexes

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open scoped Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations

section RemoveZeros
variable {J : Type*} {A : Type u} [Category.{v} A] [Preadditive A]
variable (f : J → A) (s : Set J) [Finite s]
variable (hz : ∀ j, j ∉ s → IsZero (f j))
variable [HasBiproduct (fun j : s => f j.val)]

/-- Extend a finite sub-biproduct by zero legs at the omitted zero objects. -/
def zeroExtendedBicone : Bicone f where
  pt := ⨁ (fun j : s => f j.val)
  ι j := if h : j ∈ s then biproduct.ι (fun j : s => f j.val) ⟨j, h⟩ else 0
  π j := if h : j ∈ s then biproduct.π (fun j : s => f j.val) ⟨j, h⟩ else 0
  ι_π j k := by
    classical
    by_cases hj : j ∈ s
    · by_cases hk : k ∈ s
      · simp only [dite_eq_left hj, dite_eq_left hk]
        by_cases h : j = k
        · subst k
          simp
        · rw [biproduct.ι_π_ne _ (show (⟨j, hj⟩ : s) ≠ ⟨k, hk⟩ from
            fun e => h (congrArg Subtype.val e)), dite_eq_right h]
      · have hne : j ≠ k := fun h => hk (h ▸ hj)
        rw [dite_eq_right hk, comp_zero, dite_eq_right hne]
    · rw [dite_eq_right hj, zero_comp]
      split_ifs with h
      · subst k
        exact (hz j hj).eq_of_src _ _
      · rfl

/-- Removing zero terms preserves both universal properties, including when
there are no nonzero terms. -/
def zeroExtendedIsBilimit : (zeroExtendedBicone f s hz).IsBilimit where
  isLimit := Fan.IsLimit.mk _
    (fun c => biproduct.lift (fun j : s => c.proj j.val))
    (by
      intro c j
      by_cases hj : j ∈ s
      · simp [zeroExtendedBicone, hj, Fan.proj]
      · exact (hz j hj).eq_of_tgt _ _)
    (by
      intro c m hm
      apply biproduct.hom_ext (f := fun j : s => f j.val)
      intro j
      simpa [zeroExtendedBicone, j.property] using hm j.val)
  isColimit := Cofan.IsColimit.mk _
    (fun c => biproduct.desc (fun j : s => c.inj j.val))
    (by
      intro c j
      by_cases hj : j ∈ s
      · simp [zeroExtendedBicone, hj, Cofan.inj]
      · exact (hz j hj).eq_of_src _ _)
    (by
      intro c m hm
      apply biproduct.hom_ext' (f := fun j : s => f j.val)
      intro j
      simpa [zeroExtendedBicone, j.property] using hm j.val)

end RemoveZeros

/-- A finitely supported family in an additive category has its full
(possibly infinitely indexed) biproduct. -/
theorem hasBiproduct_of_finite_nonzero
    {J : Type*} {A : Type u} [Category.{v} A] [Preadditive A]
    [HasFiniteBiproducts A] (f : J → A)
    (hf : {j | ¬ IsZero (f j)}.Finite) : HasBiproduct f := by
  classical
  let s := {j | ¬ IsZero (f j)}
  let : Finite s := hf
  have hz : ∀ j, j ∉ s → IsZero (f j) := by
    intro j hj
    exact not_not.mp hj
  exact HasBiproduct.mk ⟨zeroExtendedBicone f s hz, zeroExtendedIsBilimit f s hz⟩

theorem diagonalBiproducts : Specs.DiagonalBiproducts.{v,u} := by
  intro A _ _ K h n
  exact hasBiproduct_of_finite_nonzero (diagonalFamily K n) (h n)

theorem quadrantFinite : Specs.QuadrantFinite.{v,u} := by
  intro A _ _ K p₀ q₀ h n
  let s : Set (Diagonal n) := {i | ¬ IsZero (diagonalFamily K n i)}
  have hp : ∀ i ∈ s, p₀ ≤ i.val.1 ∧ i.val.1 ≤ n - q₀ := by
    intro i hi
    have hb : p₀ ≤ i.val.1 ∧ q₀ ≤ i.val.2 := by
      by_contra hb
      exact hi (h i.val.1 i.val.2 hb)
    have he := i.property
    exact ⟨hb.1, by omega⟩
  have ht : Set.Finite ((fun i : Diagonal n => i.val.1) '' s) :=
    (Set.finite_Icc p₀ (n - q₀)).subset (by
      rintro _ ⟨i, hi, rfl⟩
      exact hp i hi)
  apply Set.Finite.of_finite_image ht
  intro i hi j hj hij
  apply Subtype.ext
  apply Prod.ext hij
  have hi' : i.val.1 + i.val.2 = n := i.property
  have hj' : j.val.1 + j.val.2 = n := j.property
  dsimp at hij
  omega

open DoubleTotalization

/-- Both infinite-indexed diagonal constructions exist under exactly the
finite-nonzero-support hypothesis. -/
theorem totalizationsExist : Specs.TotalizationsExist.{v,u} := by
  intro A _ _ K h
  let : ∀ n, HasBiproduct (diagonalFamily K n) := diagonalBiproducts K h
  have hs : K.HasTotal (ComplexShape.up ℤ) := by
    intro n
    change HasCoproduct (diagonalFamily K n)
    infer_instance
  have hp : HasProductTotal K := (productExistence K).mpr (fun n => inferInstance)
  exact ⟨hs, hp⟩

section Projections
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
variable [∀ n, HasBiproduct (diagonalFamily K n)]

/-- Identify the full diagonal coproduct with its biproduct. -/
def sumBiproductIso (n : ℤ) : (sumTotal K).X n ≅ ⨁ (diagonalFamily K n) :=
  (biproduct.isoCoproduct (diagonalFamily K n)).symm

@[reassoc (attr := simp)]
theorem injection_sumBiproductIso (n : ℤ) (i : Diagonal n) :
    sumInjection K i.val.1 i.val.2 n i.property ≫ (sumBiproductIso K n).hom =
      biproduct.ι (diagonalFamily K n) i := by
  change Sigma.ι (diagonalFamily K n) i ≫
    (biproduct.isoCoproduct (diagonalFamily K n)).inv = _
  simp

/-- The diagonal coordinate projection on the sum totalization. -/
def sumProjection (p q n : ℤ) (h : p + q = n) :
    (sumTotal K).X n ⟶ (K.X p).X q :=
  (sumBiproductIso K n).hom ≫ biproduct.π (diagonalFamily K n) ⟨(p, q), h⟩

@[reassoc (attr := simp)]
theorem injection_sumProjection_self (p q n : ℤ) (h : p + q = n) :
    sumInjection K p q n h ≫ sumProjection K p q n h = 𝟙 _ := by
  rw [sumProjection, ← Category.assoc,
    injection_sumBiproductIso K n ⟨(p, q), h⟩, biproduct.ι_π_self]

@[reassoc (attr := simp)]
theorem injection_sumProjection_ne (p q r s n : ℤ) (h : p + q = n)
    (h' : r + s = n) (hne : (p, q) ≠ (r, s)) :
    sumInjection K p q n h ≫ sumProjection K r s n h' = 0 := by
  rw [sumProjection, ← Category.assoc,
    injection_sumBiproductIso K n ⟨(p, q), h⟩]
  exact biproduct.ι_π_ne (diagonalFamily K n)
    (show (⟨(p, q), h⟩ : Diagonal n) ≠ ⟨(r, s), h'⟩ from
      fun e => hne (congrArg Subtype.val e))

end Projections

section Slices
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) (hK : FiniteDiagonals K)

include hK in
theorem sliceBiproducts (n : ℤ) (P : Diagonal n → Prop) :
    HasBiproduct (Subtype.restrict P (diagonalFamily K n)) := by
  apply hasBiproduct_of_finite_nonzero
  exact (hK n).preimage (Subtype.val_injective.injOn)

variable [K.HasTotal (ComplexShape.up ℤ)]
variable [∀ n, HasBiproduct (diagonalFamily K n)]

/-- The split inclusion of any selected diagonal summands. -/
def sliceInclusion (n : ℤ) (P : Diagonal n → Prop)
    [HasBiproduct (Subtype.restrict P (diagonalFamily K n))] :
    (⨁ (Subtype.restrict P (diagonalFamily K n))) ⟶ (sumTotal K).X n :=
  biproduct.fromSubtype (diagonalFamily K n) P ≫ (sumBiproductIso K n).inv

instance sliceInclusion_mono (n : ℤ) (P : Diagonal n → Prop)
    [HasBiproduct (Subtype.restrict P (diagonalFamily K n))] :
    Mono (sliceInclusion K n P) := by
  have fac : sliceInclusion K n P ≫ ((sumBiproductIso K n).hom ≫
      biproduct.toSubtype (diagonalFamily K n) P) = 𝟙 _ := by
    simp [sliceInclusion]
  exact mono_of_mono_fac fac

@[reassoc (attr := simp)]
theorem injection_sliceInclusion (n : ℤ) (P : Diagonal n → Prop)
    [HasBiproduct (Subtype.restrict P (diagonalFamily K n))] (i : Subtype P) :
    biproduct.ι (Subtype.restrict P (diagonalFamily K n)) i ≫
      sliceInclusion K n P = sumInjection K i.val.val.1 i.val.val.2 n i.val.property := by
  rw [sliceInclusion, biproduct.ι_fromSubtype_assoc]
  apply (Iso.comp_inv_eq _).2
  exact (injection_sumBiproductIso K n i.val).symm

omit [Abelian A] in
/-- Transfer a factorization between chosen representatives to subobject arrows. -/
theorem factor_mk {B C X Y : A} (ι : B ⟶ X) (κ : C ⟶ Y)
    [Mono ι] [Mono κ] (f : X ⟶ Y) (g : B ⟶ C) (hg : g ≫ κ = ι ≫ f) :
    ∃ t : (Subobject.mk ι : A) ⟶ (Subobject.mk κ : A),
      t ≫ (Subobject.mk κ).arrow = (Subobject.mk ι).arrow ≫ f := by
  refine ⟨(Subobject.underlyingIso ι).hom ≫ g ≫ (Subobject.underlyingIso κ).inv, ?_⟩
  simp only [Category.assoc, Subobject.underlyingIso_arrow]
  rw [hg, Subobject.underlyingIso_hom_comp_eq_mk_assoc]

end Slices

section Thresholds
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)]
variable [∀ n, HasBiproduct (diagonalFamily K n)]
variable [∀ n (P : Diagonal n → Prop), HasBiproduct (Subtype.restrict P (diagonalFamily K n))]
variable (axis : ℤ × ℤ → ℤ)

abbrev threshold (a n : ℤ) : Diagonal n → Prop := fun i => a ≤ axis i.val

/-- The prescribed sub-biproduct, as a subobject of the sum total. -/
def thresholdPiece (a n : ℤ) : Subobject ((sumTotal K).X n) :=
  Subobject.mk (sliceInclusion K n (threshold axis a n))

theorem threshold_decreasing (a n : ℤ) :
    thresholdPiece K axis (a + 1) n ≤ thresholdPiece K axis a n := by
  unfold thresholdPiece
  apply Subobject.mk_le_mk_of_comm
    (biproduct.desc (f := Subtype.restrict (threshold axis (a + 1) n) (diagonalFamily K n))
      fun i => biproduct.ι (Subtype.restrict (threshold axis a n) (diagonalFamily K n))
      (⟨i.val, by have := i.property; dsimp [threshold] at *; omega⟩ :
        Subtype (threshold axis a n)))
  apply biproduct.hom_ext'
  intro i
  simp

theorem threshold_preserved
    (hh : ∀ p q, axis (p, q) ≤ axis (p + 1, q))
    (hv : ∀ p q, axis (p, q) ≤ axis (p, q + 1)) (a n : ℤ) :
    ∃ δ : (thresholdPiece K axis a n : A) ⟶ (thresholdPiece K axis a (n + 1) : A),
      δ ≫ (thresholdPiece K axis a (n + 1)).arrow =
        (thresholdPiece K axis a n).arrow ≫ (sumTotal K).d n (n + 1) := by
  let H (i : Subtype (threshold axis a n)) : Subtype (threshold axis a (n + 1)) :=
    ⟨⟨(i.val.val.1 + 1, i.val.val.2), by have := i.val.property; dsimp at *; omega⟩,
      le_trans i.property (hh _ _)⟩
  let V (i : Subtype (threshold axis a n)) : Subtype (threshold axis a (n + 1)) :=
    ⟨⟨(i.val.val.1, i.val.val.2 + 1), by have := i.val.property; dsimp at *; omega⟩,
      le_trans i.property (hv _ _)⟩
  refine factor_mk _ _ _ (biproduct.desc (fun i =>
    (K.d i.val.val.1 (i.val.val.1 + 1)).f i.val.val.2 ≫
      biproduct.ι (Subtype.restrict (threshold axis a (n + 1)) (diagonalFamily K (n + 1))) (H i) +
      (ComplexShape.up ℤ).ε i.val.val.1 •
        ((K.X i.val.val.1).d i.val.val.2 (i.val.val.2 + 1) ≫
          biproduct.ι (Subtype.restrict (threshold axis a (n + 1)) (diagonalFamily K (n + 1))) (V i)))) ?_
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct.ι_desc_assoc, Preadditive.add_comp, Category.assoc,
    Linear.units_smul_comp, injection_sliceInclusion, injection_sliceInclusion_assoc]
  exact (sumDifferential K _ _ _ _ _ _ rfl rfl i.val.property
    (H i).val.property (V i).val.property).symm

/-- Both coordinate axes satisfy these monotonicity conditions. -/
def axisFiltration
    (hh : ∀ p q, axis (p, q) ≤ axis (p + 1, q))
    (hv : ∀ p q, axis (p, q) ≤ axis (p, q + 1)) : Filtration (sumTotal K) :=
  Filtration.ofSuccessive (thresholdPiece K axis)
    (threshold_decreasing K axis) (threshold_preserved K axis hh hv)

theorem axisFiltration_formula
    (hh : ∀ p q, axis (p, q) ≤ axis (p + 1, q))
    (hv : ∀ p q, axis (p, q) ≤ axis (p, q + 1)) :
    HasFiltrationFormula K axis (axisFiltration K axis hh hv) := by
  intro a n
  let : HasBiproduct (fun i : {i : Diagonal n // a ≤ axis i.val} =>
      diagonalFamily K n i.val) :=
    inferInstanceAs (HasBiproduct (Subtype.restrict (threshold axis a n) (diagonalFamily K n)))
  refine ⟨biproduct.bicone _, biproduct.isBilimit _,
    sliceInclusion K n (threshold axis a n), inferInstance, rfl, ?_⟩
  intro i
  exact injection_sliceInclusion K n (threshold axis a n) i

theorem threshold_eq_top (a n : ℤ)
    (ha : ∀ i : Diagonal n, ¬ IsZero (diagonalFamily K n i) → a ≤ axis i.val) :
    thresholdPiece K axis a n = ⊤ := by
  let r := (sumBiproductIso K n).hom ≫
    biproduct.toSubtype (diagonalFamily K n) (threshold axis a n)
  have h₁ : sliceInclusion K n (threshold axis a n) ≫ r = 𝟙 _ := by
    simp [r, sliceInclusion]
  have h₂ : r ≫ sliceInclusion K n (threshold axis a n) = 𝟙 _ := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    let i : Diagonal n := ⟨(p,q), hpq⟩
    by_cases hi : threshold axis a n i
    · change sumInjection K p q n hpq ≫ (r ≫ sliceInclusion K n (threshold axis a n)) = _
      dsimp only [r]
      simp only [Category.assoc]
      rw [injection_sumBiproductIso_assoc K n ⟨(p,q), hpq⟩,
        biproduct.ι_toSubtype_assoc, dite_eq_left hi,
        injection_sliceInclusion, Category.comp_id]
    · exact (show IsZero ((K.X p).X q) from
        by by_contra hz; exact hi (ha i hz)).eq_of_src _ _
  let e : (⨁ Subtype.restrict (threshold axis a n) (diagonalFamily K n)) ≅
      (sumTotal K).X n := ⟨sliceInclusion K n (threshold axis a n), r, h₁, h₂⟩
  have : IsIso (sliceInclusion K n (threshold axis a n)) :=
    e.isIso_hom
  exact Subobject.mk_eq_top_of_isIso (sliceInclusion K n (threshold axis a n))

theorem threshold_eq_bot (a n : ℤ)
    (ha : ∀ i : Diagonal n, a ≤ axis i.val → IsZero (diagonalFamily K n i)) :
    thresholdPiece K axis a n = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.mpr
  apply biproduct.hom_ext'
  intro i
  exact (ha i.val i.property).eq_of_src _ _

theorem axisFiltration_finite (hK : FiniteDiagonals K)
    (hh : ∀ p q, axis (p, q) ≤ axis (p + 1, q))
    (hv : ∀ p q, axis (p, q) ≤ axis (p, q + 1)) :
    DegreewiseFinite (axisFiltration K axis hh hv) := by
  intro n
  have hf := (hK n).image (fun i : Diagonal n => axis i.val)
  obtain ⟨l, hl⟩ := hf.bddBelow
  obtain ⟨u, hu⟩ := hf.bddAbove
  refine ⟨l, u + 1, fun a => ⟨?_, ?_⟩⟩
  · intro ha
    apply threshold_eq_top
    intro i hi
    exact ha.trans (hl (Set.mem_image_of_mem _ hi))
  · intro ha
    apply threshold_eq_bot
    intro i hi
    by_contra hz
    have := hu (Set.mem_image_of_mem (fun i : Diagonal n => axis i.val) hz)
    omega

end Thresholds

theorem filtrations : Specs.Filtrations.{v,u} := by
  intro A _ _ K hK _
  let : ∀ n, HasBiproduct (diagonalFamily K n) := diagonalBiproducts K hK
  let : ∀ n (P : Diagonal n → Prop), HasBiproduct (Subtype.restrict P (diagonalFamily K n)) :=
    sliceBiproducts K hK
  refine ⟨axisFiltration K Prod.fst (by intros; dsimp; omega) (by intros; exact le_rfl),
    axisFiltration K Prod.snd (by intros; exact le_rfl) (by intros; dsimp; omega),
    axisFiltration_formula K _ _ _, axisFiltration_formula K _ _ _,
    axisFiltration_finite K _ hK _ _, axisFiltration_finite K _ hK _ _⟩

section Naturality
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K L : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]

theorem formula_filteredMap (axis : ℤ × ℤ → ℤ)
    (F : Filtration (sumTotal K)) (G : Filtration (sumTotal L))
    (hF : HasFiltrationFormula K axis F) (hG : HasFiltrationFormula L axis G) (f : K ⟶ L) :
    ∃ g : FilteredMap ⟨sumTotal K, F⟩ ⟨sumTotal L, G⟩,
      g.hom = HomologicalComplex₂.total.map f (ComplexShape.up ℤ) := by
  refine ⟨⟨HomologicalComplex₂.total.map f (ComplexShape.up ℤ), ?_⟩, rfl⟩
  intro a n
  obtain ⟨b, hb, ι, hι, eι, hbi⟩ := hF a n
  obtain ⟨c, hc, κ, hκ, eκ, hci⟩ := hG a n
  rw [← eι, ← eκ]
  let g := hb.isColimit.desc (Cofan.mk c.pt (fun i =>
    (f.f i.val.val.1).f i.val.val.2 ≫ c.ι i))
  apply factor_mk ι κ _ g
  apply hb.isColimit.hom_ext
  rintro ⟨i⟩
  change b.ι i ≫ (g ≫ κ) = b.ι i ≫ (ι ≫ _)
  rw [← Category.assoc, show b.ι i ≫ g =
      (f.f i.val.val.1).f i.val.val.2 ≫ c.ι i from
      hb.isColimit.fac _ ⟨i⟩,
    Category.assoc, hci i, ← Category.assoc, hbi i]
  exact (HomologicalComplex₂.ιTotal_map K L f _ _ _ _ _).symm

end Naturality

theorem naturality : Specs.Naturality.{v,u} := by
  intro A _ _ K L _ _ Fc Fr Gc Gr hc hr hgc hgr f
  exact ⟨formula_filteredMap K L _ _ _ hc hgc f,
    formula_filteredMap K L _ _ _ hr hgr f⟩


section Comparison
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (K : Bicomplex A) [K.HasTotal (ComplexShape.up ℤ)] [HasProductTotal K]
variable [∀ n, HasBiproduct (diagonalFamily K n)]

omit [K.HasTotal (ComplexShape.up ℤ)] [∀ n, HasBiproduct (diagonalFamily K n)] in
theorem product_hom_ext {n : ℤ} {B : A} {f g : B ⟶ (productTotal K).X n}
    (h : ∀ p q (hpq : p + q = n),
      f ≫ productProjection K p q n hpq = g ≫ productProjection K p q n hpq) : f = g := by
  apply Quiver.Hom.op_inj
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  apply Quiver.Hom.unop_inj
  exact h p q hpq

/-- Identify the diagonal product with the same biproduct. -/
def productBiproductIso (n : ℤ) : (productTotal K).X n ≅ ⨁ (diagonalFamily K n) where
  hom := biproduct.lift (fun i => productProjection K i.val.1 i.val.2 n i.property)
  inv := (productUniversal K n (⨁ (diagonalFamily K n))
    (fun p q h => biproduct.π (diagonalFamily K n) ⟨(p,q),h⟩)).choose
  hom_inv_id := by
    apply product_hom_ext K
    intro p q h
    rw [Category.assoc,
      (productUniversal K n (⨁ (diagonalFamily K n))
        (fun p q h => biproduct.π (diagonalFamily K n) ⟨(p,q),h⟩)).choose_spec.1 p q h]
    simp
  inv_hom_id := by
    apply biproduct.hom_ext
    intro i
    rw [Category.assoc, biproduct.lift_π]
    exact ((productUniversal K n (⨁ (diagonalFamily K n))
      (fun p q h => biproduct.π (diagonalFamily K n) ⟨(p,q),h⟩)).choose_spec.1
        i.val.1 i.val.2 i.property).trans (by simp)

@[reassoc (attr := simp)]
theorem productBiproductIso_inv_projection (n : ℤ) (i : Diagonal n) :
    (productBiproductIso K n).inv ≫ productProjection K i.val.1 i.val.2 n i.property =
      biproduct.π (diagonalFamily K n) i :=
  (productUniversal K n _ _).choose_spec.1 i.val.1 i.val.2 i.property

/-- Degreewise canonical comparison. -/
def comparisonIsoX (n : ℤ) : (sumTotal K).X n ≅ (productTotal K).X n :=
  sumBiproductIso K n ≪≫ (productBiproductIso K n).symm

@[reassoc (attr := simp)]
theorem comparisonIsoX_projection (p q n : ℤ) (h : p + q = n) :
    (comparisonIsoX K n).hom ≫ productProjection K p q n h = sumProjection K p q n h := by
  simp only [comparisonIsoX, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [productBiproductIso_inv_projection K n ⟨(p,q), h⟩]
  rfl

@[reassoc (attr := simp)]
theorem injection_comparison_self (p q n : ℤ) (h : p + q = n) :
    sumInjection K p q n h ≫ (comparisonIsoX K n).hom ≫ productProjection K p q n h = 𝟙 _ := by
  rw [comparisonIsoX_projection, injection_sumProjection_self]

@[reassoc (attr := simp)]
theorem injection_comparison_ne (p q r s n : ℤ) (h : p + q = n)
    (h' : r + s = n) (hne : (p, q) ≠ (r, s)) :
    sumInjection K p q n h ≫ (comparisonIsoX K n).hom ≫ productProjection K r s n h' = 0 := by
  rw [comparisonIsoX_projection, injection_sumProjection_ne K p q r s n h h' hne]

/-- The identity/zero diagonal matrices intertwine the total differentials. -/
theorem comparison_comm_successive (n : ℤ) :
    (comparisonIsoX K n).hom ≫ (productTotal K).d n (n + 1) =
      (sumTotal K).d n (n + 1) ≫ (comparisonIsoX K (n + 1)).hom := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  apply product_hom_ext K
  intro r s hrs
  have hpq' : p + q = n := hpq
  have hrs' : r + s = n + 1 := hrs
  have hh : (p + 1) + q = n + 1 := by omega
  have hv : p + (q + 1) = n + 1 := by omega
  have hh' : (r - 1) + s = n := by omega
  have hv' : r + (s - 1) = n := by omega
  have hout := congrArg (fun t => t ≫ (comparisonIsoX K (n + 1)).hom ≫
      productProjection K r s (n + 1) hrs')
    (sumDifferential K p (p + 1) q (q + 1) n (n + 1) rfl rfl hpq' hh hv)
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc] at hout
  change (sumInjection K p q n hpq' ≫
      ((comparisonIsoX K n).hom ≫ (productTotal K).d n (n + 1))) ≫
        productProjection K r s (n + 1) hrs' =
    (sumInjection K p q n hpq' ≫
      ((sumTotal K).d n (n + 1) ≫ (comparisonIsoX K (n + 1)).hom)) ≫
        productProjection K r s (n + 1) hrs'
  simp only [Category.assoc]
  rw [hout]
  by_cases hr : r = p + 1
  · have hs : s = q := by omega
    subst r s
    rw [productDifferential K (p + 1) p q (q - 1) n (n + 1)
      rfl (by dsimp [ComplexShape.up]; omega) hrs' hpq' hv']
    simp only [Preadditive.comp_add, Linear.comp_units_smul]
    simp [show (p,q) ≠ (p+1,q-1) by
        intro h; have := congrArg Prod.fst h; dsimp at this; omega,
      show (p,q+1) ≠ (p+1,q) by
        intro h; have := congrArg Prod.fst h; dsimp at this; omega]
  · by_cases hr' : r = p
    · have hs : s = q + 1 := by omega
      subst r s
      rw [productDifferential K p (p - 1) (q + 1) q n (n + 1)
        (by dsimp [ComplexShape.up]; omega) rfl hrs' hh' hpq']
      simp only [Preadditive.comp_add, Linear.comp_units_smul]
      simp [show (p,q) ≠ (p-1,q+1) by
          intro h; have := congrArg Prod.fst h; dsimp at this; omega,
        show (p+1,q) ≠ (p,q+1) by
          intro h; have := congrArg Prod.fst h; dsimp at this; omega]
    · rw [productDifferential K r (r - 1) s (s - 1) n (n + 1)
        (by dsimp [ComplexShape.up]; omega) (by dsimp [ComplexShape.up]; omega) hrs' hh' hv']
      simp only [Preadditive.comp_add, Linear.comp_units_smul]
      simp [show (p,q) ≠ (r-1,s) by
          intro h; have := congrArg Prod.fst h; dsimp at this; omega,
        show (p,q) ≠ (r,s-1) by
          intro h; exact hr' (congrArg Prod.fst h).symm,
        show (p+1,q) ≠ (r,s) by
          intro h; exact hr (congrArg Prod.fst h).symm,
        show (p,q+1) ≠ (r,s) by
          intro h; exact hr' (congrArg Prod.fst h).symm]

/-- Canonical sum-to-product isomorphism of cochain complexes. -/
def comparisonIso : sumTotal K ≅ productTotal K :=
  HomologicalComplex.Hom.isoOfComponents (comparisonIsoX K) (by
    intro n m hnm
    have : n + 1 = m := hnm
    subst m
    exact comparison_comm_successive K n)

end Comparison

theorem comparison : Specs.Comparison.{v,u} := by
  intro A _ _ K hK _ _
  let : ∀ n, HasBiproduct (diagonalFamily K n) := diagonalBiproducts K hK
  refine ⟨comparisonIso K, ?_⟩
  intro n i j
  change sumInjection K i.val.1 i.val.2 n i.property ≫
    (comparisonIsoX K n).hom ≫ productProjection K j.val.1 j.val.2 n j.property = _
  by_cases h : i = j
  · subst j
    simp
  · rw [injection_comparison_ne K _ _ _ _ _ _ _
      (fun e => h (Subtype.ext e)), dite_eq_right h]

end AdvancedHomologicalAlgebra.FiniteDiagonalFiltrations
