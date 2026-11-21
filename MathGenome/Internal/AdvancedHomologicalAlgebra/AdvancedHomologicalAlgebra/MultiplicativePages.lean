import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.PageCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MultiplicativePages
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! HA-S06: representative calculations for the multiplicative construction.
Products and their laws are constructed on the actual categorical pages.
The canonical next-page and stable comparisons are proved below.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe u v
namespace AdvancedHomologicalAlgebra
namespace MultiplicativePages
variable {R : Type u} [CommRing R]

@[simp]
theorem mem_carrier_iff {M : ModuleCat.{v} R} (S : Subobject M) (x : M) :
    x ∈ carrier S ↔ ∃ a : (S : ModuleCat R), S.arrow a = x := Iff.rfl

@[simp]
theorem mem_carrier_inf {M : ModuleCat.{v} R} (S T : Subobject M) (x : M) :
    x ∈ carrier (S ⊓ T) ↔ x ∈ carrier S ∧ x ∈ carrier T := by
  change x ∈ ModuleCat.subobjectModule M (S ⊓ T) ↔ _
  rw [(ModuleCat.subobjectModule M).map_inf]
  rfl

@[simp]
theorem mem_carrier_pullback {M N : ModuleCat.{v} R} (f : M ⟶ N)
    (S : Subobject N) (x : M) :
    x ∈ carrier ((Subobject.pullback f).obj S) ↔ f x ∈ carrier S := by
  rw [mem_carrier_iff, mem_carrier_iff]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨Subobject.pullbackπ f S a, ?_⟩
    exact ConcreteCategory.congr_hom (Subobject.isPullback f S).w a
  · rintro ⟨a, ha⟩
    obtain ⟨b, _, hb⟩ := Types.exists_of_isPullback
      ((Subobject.isPullback f S).map (forget (ModuleCat R))) a x ha
    exact ⟨b, hb⟩

/-- Transport along a degree equality preserves membership in the same filtration. -/
@[simp]
theorem reindex_mem_piece {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : Filtration K)
    {i j : ℤ} (h : i = j) (p : ℤ) (x : K.X i) :
    (eqToHom (congrArg K.X h)) x ∈ carrier (F.piece p j) ↔
      x ∈ carrier (F.piece p i) := by
  subst j
  rfl

@[simp]
theorem mem_carrier_sup {M : ModuleCat.{v} R} (S T : Subobject M) (x : M) :
    x ∈ carrier (S ⊔ T) ↔ ∃ a ∈ carrier S, ∃ b ∈ carrier T, a+b = x := by
  change x ∈ ModuleCat.subobjectModule M (S ⊔ T) ↔ _
  rw [(ModuleCat.subobjectModule M).map_sup]
  exact Submodule.mem_sup

@[simp]
theorem mem_carrier_image {M N : ModuleCat.{v} R} (f : M ⟶ N) (y : N) :
    y ∈ carrier (imageSubobject f) ↔ ∃ x, f x = y := by
  rw [mem_carrier_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
      (factorThruImageSubobject f)).1 inferInstance a
    exact ⟨x, (ConcreteCategory.congr_hom (imageSubobject_arrow_comp f) x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨factorThruImageSubobject f x,
      ConcreteCategory.congr_hom (imageSubobject_arrow_comp f) x⟩

/-- The kernel of a categorical cokernel projection is its concrete image. -/
theorem cokernel_π_eq_zero_iff {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : N) :
    cokernel.π f x = 0 ↔ x ∈ LinearMap.range f.hom := by
  let e := (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv
  rw [← e.map_eq_zero_iff]
  change (ModuleCat.cokernelIsoRangeQuotient f).hom (cokernel.π f x) = 0 ↔ _
  rw [← ConcreteCategory.comp_apply, ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  change (Submodule.Quotient.mk x : N ⧸ f.hom.range) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero f.hom.range

/-- Bilinear descent along two surjective linear maps needs no flatness assumption. -/
def descendBilinear {M N Q M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R Q] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (b : M →ₗ[R] N →ₗ[R] Q) (hfb : f.ker ≤ b.ker) (hgb : g.ker ≤ b.flip.ker) :
    M' →ₗ[R] N' →ₗ[R] Q :=
  (b.liftQ₂ f.ker g.ker hfb hgb).compl₁₂
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
    (g.quotKerEquivOfSurjective hg).symm.toLinearMap

@[simp]
theorem descendBilinear_apply {M N Q M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R Q] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (b : M →ₗ[R] N →ₗ[R] Q) (hfb : f.ker ≤ b.ker) (hgb : g.ker ≤ b.flip.ker)
    (x : M) (y : N) :
    descendBilinear f g hf hg b hfb hgb (f x) (g y) = b x y := by
  simp [descendBilinear]

/-- The categorical almost cycles have precisely the original element description. -/
theorem mem_almost_iff {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : Filtration K)
    (r p n : ℤ) (x : K.X n) :
    x ∈ carrier (FilteredPage.almost F r p n) ↔
      x ∈ carrier (F.piece p n) ∧ K.d n (n+1) x ∈ carrier (F.piece (p+r) (n+1)) := by
  simp only [FilteredPage.almost, mem_carrier_inf, mem_carrier_pullback]

/-- The numerator multiplication calculation does not use commutativity of the DGA. -/
theorem mul_mem_almost {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (B : Algebra K) (F : Filtration K) (hF : Compatible B F)
    (r p n s m : ℤ) (x : K.X n) (y : K.X m)
    (hx : x ∈ carrier (FilteredPage.almost F r p n))
    (hy : y ∈ carrier (FilteredPage.almost F r s m)) :
    B.mul n m x y ∈ carrier (FilteredPage.almost F r (p+s) (n+m)) := by
  obtain ⟨hx, hdx⟩ := (mem_almost_iff F r p n x).1 hx
  obtain ⟨hy, hdy⟩ := (mem_almost_iff F r s m y).1 hy
  apply (mem_almost_iff F r (p+s) (n+m) _).2
  refine ⟨hF.mul_mem p n s m x y hx hy, ?_⟩
  rw [B.leibniz]
  apply Submodule.add_mem
  · have h := hF.mul_mem (p+r) (n+1) s m (K.d n (n+1) x) y hdx hy
    have hp : (p+r)+s = (p+s)+r := by omega
    rw [reindex_mem_piece F (by omega : (n+1)+m = n+m+1)]
    simpa only [hp] using h
  · apply Submodule.smul_mem
    have h := hF.mul_mem p n (s+r) (m+1) x (K.d m (m+1) y) hx hdy
    have hp : p+(s+r) = (p+s)+r := by omega
    rw [reindex_mem_piece F (by omega : n+(m+1) = n+m+1)]
    simpa only [hp] using h

/-- The source's alternate denominator detects zero classes on the actual pages.
The accepted HA-F03 construction proves this presentation even at `r = 0`. -/
theorem toPage_eq_zero_iff {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : Filtration K)
    (r p n : ℤ) (h : FilteredPage.boundaries F r p n ≤ FilteredPage.cycles F r p n)
    (x : (FilteredPage.almost F r p n : ModuleCat R)) :
    FilteredPage.toPage F r p n h x = 0 ↔
      (FilteredPage.almost F r p n).arrow x ∈ carrier (FilteredPage.denominator F r p n) := by
  let d := Subobject.ofLE _ _ (FilteredPage.denominator_le F r p n)
  let e := (FilteredPage.quotientIso F r p n h).toLinearEquiv
  have he : e (cokernel.π d x) = FilteredPage.toPage F r p n h x :=
    ConcreteCategory.congr_hom (FilteredPage.toAlternate_quotientIso F r p n h) x
  rw [← he, e.map_eq_zero_iff, cokernel_π_eq_zero_iff, mem_carrier_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (ConcreteCategory.congr_hom
      (Subobject.ofLE_arrow (FilteredPage.denominator_le F r p n)) a).symm.trans
        (congrArg (FilteredPage.almost F r p n).arrow ha)⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (ModuleCat.mono_iff_injective (FilteredPage.almost F r p n).arrow).1 inferInstance
    exact (ConcreteCategory.congr_hom
      (Subobject.ofLE_arrow (FilteredPage.denominator_le F r p n)) a).trans ha

/-- An actual subobject is linearly equivalent to the range of its inclusion. -/
def carrierEquiv {M : ModuleCat.{v} R} (S : Subobject M) :
    (S : ModuleCat R) ≃ₗ[R] carrier S :=
  LinearEquiv.ofInjective S.arrow.hom ((ModuleCat.mono_iff_injective S.arrow).1 inferInstance)

@[simp]
theorem arrow_carrierEquiv_symm {M : ModuleCat.{v} R} (S : Subobject M) (x : carrier S) :
    S.arrow ((carrierEquiv S).symm x) = x := by
  exact congrArg Subtype.val ((carrierEquiv S).apply_symm_apply x)

/-- Restrict a bilinear map to three categorical subobjects. -/
def restrictBilinear {M N Q : ModuleCat.{v} R}
    (S : Subobject M) (T : Subobject N) (U : Subobject Q)
    (b : M →ₗ[R] N →ₗ[R] Q)
    (hb : ∀ x y, x ∈ carrier S → y ∈ carrier T → b x y ∈ carrier U) :
    (S : ModuleCat R) →ₗ[R] (T : ModuleCat R) →ₗ[R] (U : ModuleCat R) where
  toFun x :=
    { toFun := fun y => (carrierEquiv U).symm ⟨b (S.arrow x) (T.arrow y), hb _ _ ⟨x, rfl⟩ ⟨y, rfl⟩⟩
      map_add' y z := by
        apply (ModuleCat.mono_iff_injective U.arrow).1 inferInstance
        simp only [map_add, arrow_carrierEquiv_symm]
      map_smul' a y := by
        apply (ModuleCat.mono_iff_injective U.arrow).1 inferInstance
        simp only [map_smul, arrow_carrierEquiv_symm, RingHom.id_apply] }
  map_add' x y := by
    ext z
    apply (ModuleCat.mono_iff_injective U.arrow).1 inferInstance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      map_add, arrow_carrierEquiv_symm]
  map_smul' a x := by
    ext y
    apply (ModuleCat.mono_iff_injective U.arrow).1 inferInstance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      map_smul, arrow_carrierEquiv_symm, RingHom.id_apply]

@[simp] theorem restrictBilinear_arrow {M N Q : ModuleCat.{v} R}
    (S : Subobject M) (T : Subobject N) (U : Subobject Q)
    (b : M →ₗ[R] N →ₗ[R] Q)
    (hb : ∀ x y, x ∈ carrier S → y ∈ carrier T → b x y ∈ carrier U)
    (x : (S : ModuleCat R)) (y : (T : ModuleCat R)) :
    U.arrow (restrictBilinear S T U b hb x y) = b (S.arrow x) (T.arrow y) :=
  arrow_carrierEquiv_symm _ _

/-- A bilinear lift of multiplication to the actual HA-F03 almost-cycle objects. -/
def almostMul {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (B : Algebra K) (F : Filtration K) (hF : Compatible B F) (r p n s m : ℤ) :
    (FilteredPage.almost F r p n : ModuleCat R) →ₗ[R]
    (FilteredPage.almost F r s m : ModuleCat R) →ₗ[R]
    (FilteredPage.almost F r (p+s) (n+m) : ModuleCat R) where
  toFun x :=
    { toFun := fun y => (carrierEquiv _).symm
        ⟨B.mul n m ((FilteredPage.almost F r p n).arrow x)
          ((FilteredPage.almost F r s m).arrow y),
          mul_mem_almost B F hF r p n s m _ _ ⟨x, rfl⟩ ⟨y, rfl⟩⟩
      map_add' y z := by
        apply (ModuleCat.mono_iff_injective (FilteredPage.almost F r (p+s) (n+m)).arrow).1
          inferInstance
        simp only [map_add, arrow_carrierEquiv_symm]
      map_smul' a y := by
        apply (ModuleCat.mono_iff_injective (FilteredPage.almost F r (p+s) (n+m)).arrow).1
          inferInstance
        simp only [map_smul, arrow_carrierEquiv_symm, RingHom.id_apply] }
  map_add' x y := by
    ext z
    apply (ModuleCat.mono_iff_injective (FilteredPage.almost F r (p+s) (n+m)).arrow).1
      inferInstance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      map_add, arrow_carrierEquiv_symm]
  map_smul' a x := by
    ext y
    apply (ModuleCat.mono_iff_injective (FilteredPage.almost F r (p+s) (n+m)).arrow).1
      inferInstance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      map_smul, arrow_carrierEquiv_symm, RingHom.id_apply]

@[simp]
theorem almostMul_arrow {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (B : Algebra K) (F : Filtration K) (hF : Compatible B F) (r p n s m : ℤ)
    (x : (FilteredPage.almost F r p n : ModuleCat R))
    (y : (FilteredPage.almost F r s m : ModuleCat R)) :
    (FilteredPage.almost F r (p+s) (n+m)).arrow (almostMul B F hF r p n s m x y) =
      B.mul n m ((FilteredPage.almost F r p n).arrow x)
        ((FilteredPage.almost F r s m).arrow y) := by
  exact arrow_carrierEquiv_symm _ _

section Units
variable {K : CochainComplex (ModuleCat.{v} R) ℤ}
theorem unit_closed_of_laws (B : Algebra K) (e : K.X 0)
    (hl : ∀ n (x : K.X n), HEq (B.mul 0 n e x) x)
    (hr : ∀ n (x : K.X n), HEq (B.mul n 0 x e) x) : K.d 0 1 e = 0 := by
  have h := B.leibniz 0 0 e e
  have he : B.mul 0 0 e e = e := eq_of_heq (hl 0 e)
  rw [he] at h
  have h₁ :
      (eqToHom (congrArg K.X (by omega : ((0 : ℤ)+1)+0 = 0+0+1)))
        (B.mul (0+1) 0 (K.d 0 (0+1) e) e) = K.d 0 1 e := by
    change B.mul 1 0 (K.d 0 1 e) e = K.d 0 1 e
    exact eq_of_heq (hr 1 _)
  have h₂ :
      (eqToHom (congrArg K.X (by omega : (0 : ℤ)+(0+1) = 0+0+1)))
        (B.mul 0 (0+1) e (K.d 0 (0+1) e)) = K.d 0 1 e := by
    change B.mul 0 1 e (K.d 0 1 e) = K.d 0 1 e
    exact eq_of_heq (hl 1 _)
  rw [h₁, h₂] at h
  simp only [sign, Int.natAbs_zero, pow_zero, one_smul] at h
  exact (add_left_cancel ((add_zero (K.d 0 1 e)).trans h)).symm

/-- An ordinary homogeneous two-sided unit is automatically closed. -/
def Unit.ofLaws (B : Algebra K) (e : K.X 0)
    (hl : ∀ n (x : K.X n), HEq (B.mul 0 n e x) x)
    (hr : ∀ n (x : K.X n), HEq (B.mul n 0 x e) x) : Unit B where
  one := e
  closed := unit_closed_of_laws B e hl hr
  left := hl
  right := hr

end Units

section Denominator
variable {K : CochainComplex (ModuleCat.{v} R) ℤ}
variable (B : Algebra K) (F : Filtration K) (hF : Compatible B F)
open FilteredPage

/-- Monotonicity of the concrete filtration carriers. -/
theorem piece_mem_mono {p q n : ℤ} (h : p ≤ q) {x : K.X n}
    (hx : x ∈ carrier (F.piece q n)) : x ∈ carrier (F.piece p n) :=
  (ModuleCat.subobjectModule (K.X n)).monotone (antitone_int_of_succ_le (f := fun q : ℤ => F.piece q n) (fun p => F.decreasing p n) h) hx

/-- Degree transport for homogeneous elements. -/
abbrev degreeCast {i j : ℤ} (h : i = j) (x : K.X i) : K.X j :=
  (eqToHom (congrArg K.X h)) x

theorem degreeCast_heq {i j : ℤ} (h : i = j) (x : K.X i) :
    HEq (degreeCast (K := K) h x) x := by
  subst j; rfl

@[simp] theorem degreeCast_rfl {i : ℤ} (x : K.X i) : degreeCast (K := K) rfl x = x := rfl

@[simp] theorem degreeCast_cast {i j k : ℤ} (h : i = j) (h' : j = k) (x : K.X i) :
    degreeCast h' (degreeCast (K := K) h x) = degreeCast (h.trans h') x := by
  subst j; subst k; rfl

@[simp] theorem degreeCast_add {i j : ℤ} (h : i = j) (x y : K.X i) :
    degreeCast (K := K) h (x+y) = degreeCast h x + degreeCast h y := map_add _ _ _

@[simp] theorem degreeCast_smul {i j : ℤ} (h : i = j) (a : R) (x : K.X i) :
    degreeCast (K := K) h (a • x) = a • degreeCast h x := map_smul _ _ _

@[simp] theorem d_degreeCast {i j : ℤ} (h : i = j) (x : K.X i) :
    K.d j (j+1) (degreeCast h x) =
      degreeCast (congrArg (· + 1) h) (K.d i (i+1) x) := by
  subst j; rfl

@[simp] theorem mul_degreeCast {i j i' j' k : ℤ}
    (hi : i = i') (hj : j = j') (hk : i'+j' = k) (x : K.X i) (y : K.X j) :
    degreeCast hk (B.mul i' j' (degreeCast hi x) (degreeCast hj y)) =
      degreeCast (by omega : i+j = k) (B.mul i j x y) := by
  subst i'; subst j'; subst k; rfl

theorem d_mul_cast {i j k : ℤ} (h : i+j = k) (x : K.X i) (y : K.X j) :
    K.d k (k+1) (degreeCast h (B.mul i j x y)) =
      degreeCast (by omega : (i+1)+j = k+1) (B.mul (i+1) j (K.d i (i+1) x) y) +
      sign (R := R) i • degreeCast (by omega : i+(j+1) = k+1)
        (B.mul i (j+1) x (K.d j (j+1) y)) := by
  subst k; exact B.leibniz i j x y

@[simp] theorem sign_sq (i : ℤ) : sign (R := R) i * sign i = 1 := by
  simp [sign, ← mul_pow]

@[simp] theorem d_squared (n : ℤ) (x : K.X (n-1)) :
    K.d n (n+1) (K.d (n-1) n x) = 0 := by
  exact (ConcreteCategory.congr_hom (K.d_comp_d (n-1) n (n+1)) x).trans (by simp)

theorem mem_almost_iff_at (r p n k : ℤ) (h : n+1 = k) (x : K.X n) :
    x ∈ carrier (almost F r p n) ↔
      x ∈ carrier (F.piece p n) ∧ K.d n k x ∈ carrier (F.piece (p+r) k) := by
  subst k; exact mem_almost_iff F r p n x

theorem d_mul_cast_at {i j k i' j' k' : ℤ}
    (hi : i+1 = i') (hj : j+1 = j') (hk : k+1 = k') (h : i+j = k)
    (x : K.X i) (y : K.X j) :
    K.d k k' (degreeCast h (B.mul i j x y)) =
      degreeCast (by omega : i'+j = k') (B.mul i' j (K.d i i' x) y) +
      sign (R := R) i • degreeCast (by omega : i+j' = k')
        (B.mul i j' x (K.d j j' y)) := by
  subst i'; subst j'; subst k'; subst k
  exact B.leibniz i j x y

/-- The denominator consists of numerator elements differing from a restricted
boundary by an element of the next filtration step. -/
theorem mem_denominator_iff (r p n : ℤ) (x : K.X n)
    (hx : x ∈ carrier (almost F r p n)) :
    x ∈ carrier (denominator F r p n) ↔
      ∃ u : K.X (n-1), u ∈ carrier (F.piece (p-r+1) (n-1)) ∧
        K.d (n-1) n u ∈ carrier (F.piece p n) ∧
        x - K.d (n-1) n u ∈ carrier (F.piece (p+1) n) := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_carrier_sup _ _ x).1 h
    obtain ⟨u, hu⟩ := (mem_carrier_image _ b).1 hb
    have huA := (mem_almost_iff_at F (r-1) (p-r+1) (n-1) n (by omega) _).1
      (show (almost F (r-1) (p-r+1) (n-1)).arrow u ∈
        carrier (almost F (r-1) (p-r+1) (n-1)) from ⟨u, rfl⟩)
    refine ⟨(almost F (r-1) (p-r+1) (n-1)).arrow u, huA.1, ?_, ?_⟩
    · simpa only [show p-r+1+(r-1) = p by omega] using huA.2
    · have hb' : K.d (n-1) n ((almost F (r-1) (p-r+1) (n-1)).arrow u) = b := hu
      rw [hb', ← hab, add_sub_cancel_right]
      exact ((mem_almost_iff F (r-1) (p+1) n a).1 ha).1
  · rintro ⟨u, hu, hdu, hxdu⟩
    apply (mem_carrier_sup _ _ x).2
    refine ⟨x - K.d (n-1) n u, ?_, K.d (n-1) n u, ?_, sub_add_cancel _ _⟩
    · apply (mem_almost_iff F (r-1) (p+1) n _).2
      refine ⟨hxdu, ?_⟩
      simpa only [map_sub, d_squared, sub_zero, show p+1+(r-1) = p+r by omega]
        using (mem_almost_iff F r p n x).1 hx |>.2
    · apply (mem_carrier_image _ _).2
      have huA : u ∈ carrier (almost F (r-1) (p-r+1) (n-1)) := by
        apply (mem_almost_iff_at F (r-1) (p-r+1) (n-1) n (by omega) u).2
        exact ⟨hu, by simpa only [show p-r+1+(r-1) = p by omega] using hdu⟩
      obtain ⟨v, rfl⟩ := (mem_carrier_iff _ u).1 huA
      exact ⟨v, rfl⟩

include hF

/-- A zero representative in the left factor still represents zero after
multiplication by an almost cycle. -/
theorem mul_denominator_left (r p n s m : ℤ) (x : K.X n) (y : K.X m)
    (hx : x ∈ carrier (almost F r p n)) (hy : y ∈ carrier (almost F r s m))
    (hz : x ∈ carrier (denominator F r p n)) :
    B.mul n m x y ∈ carrier (denominator F r (p+s) (n+m)) := by
  obtain ⟨u, hu, hdu, hxu⟩ := (mem_denominator_iff F r p n x hx).1 hz
  obtain ⟨hyF, hdyF⟩ := (mem_almost_iff F r s m y).1 hy
  let c : K.X (n+m) := degreeCast (by omega : (n-1)+(m+1) = n+m)
    (B.mul (n-1) (m+1) u (K.d m (m+1) y))
  have hc : c ∈ carrier (F.piece (p+s+1) (n+m)) := by
    dsimp only [c]
    rw [reindex_mem_piece F (by omega : (n-1)+(m+1) = n+m)]
    have h := hF.mul_mem (p-r+1) (n-1) (s+r) (m+1) u _ hu hdyF
    simpa only [show p-r+1+(s+r)=p+s+1 by omega] using h
  let v : K.X (n+m-1) := degreeCast (by omega : (n-1)+m = n+m-1)
    (B.mul (n-1) m u y)
  have hv : v ∈ carrier (F.piece (p+s-r+1) (n+m-1)) := by
    dsimp only [v]
    rw [reindex_mem_piece F (by omega : (n-1)+m = n+m-1)]
    have h := hF.mul_mem (p-r+1) (n-1) s m u y hu hyF
    simpa only [show p-r+1+s=p+s-r+1 by omega] using h
  have hdv : K.d (n+m-1) (n+m) v =
      B.mul n m (K.d (n-1) n u) y + sign (R := R) (n-1) • c := by
    simpa only [degreeCast_rfl] using
      d_mul_cast_at B (by omega : (n-1)+1 = n) rfl
        (by omega : n+m-1+1 = n+m) (by omega : (n-1)+m = n+m-1) u y
  have hdvF : K.d (n+m-1) (n+m) v ∈ carrier (F.piece (p+s) (n+m)) := by
    rw [hdv]
    exact Submodule.add_mem _ (hF.mul_mem p n s m _ y hdu hyF)
      (Submodule.smul_mem _ _ (piece_mem_mono F (by omega) hc))
  apply (mem_denominator_iff F r (p+s) (n+m) _ (mul_mem_almost B F hF r p n s m x y hx hy)).2
  refine ⟨v, hv, hdvF, ?_⟩
  have hxy : B.mul n m (x - K.d (n-1) n u) y ∈ carrier (F.piece (p+s+1) (n+m)) := by
    have h := hF.mul_mem (p+1) n s m _ y hxu hyF
    simpa only [show p+1+s = p+s+1 by omega] using h
  have heq : B.mul n m x y - K.d (n+m-1) (n+m) v =
      B.mul n m (x - K.d (n-1) n u) y - sign (R := R) (n-1) • c := by
    rw [hdv, map_sub, LinearMap.sub_apply]
    abel
  rw [heq]
  exact Submodule.sub_mem _ hxy (Submodule.smul_mem _ _ hc)

/-- The right-factor calculation retains the order of the factors. -/
theorem mul_denominator_right (r p n s m : ℤ) (x : K.X n) (y : K.X m)
    (hx : x ∈ carrier (almost F r p n)) (hy : y ∈ carrier (almost F r s m))
    (hz : y ∈ carrier (denominator F r s m)) :
    B.mul n m x y ∈ carrier (denominator F r (p+s) (n+m)) := by
  obtain ⟨u, hu, hdu, hyu⟩ := (mem_denominator_iff F r s m y hy).1 hz
  obtain ⟨hxF, hdxF⟩ := (mem_almost_iff F r p n x).1 hx
  let c : K.X (n+m) := degreeCast (by omega : (n+1)+(m-1) = n+m)
    (B.mul (n+1) (m-1) (K.d n (n+1) x) u)
  have hc : c ∈ carrier (F.piece (p+s+1) (n+m)) := by
    dsimp only [c]
    rw [reindex_mem_piece F (by omega : (n+1)+(m-1) = n+m)]
    have h := hF.mul_mem (p+r) (n+1) (s-r+1) (m-1) _ u hdxF hu
    simpa only [show p+r+(s-r+1)=p+s+1 by omega] using h
  let v : K.X (n+m-1) := sign (R := R) n •
    degreeCast (by omega : n+(m-1) = n+m-1) (B.mul n (m-1) x u)
  have hv : v ∈ carrier (F.piece (p+s-r+1) (n+m-1)) := by
    apply Submodule.smul_mem
    rw [reindex_mem_piece F (by omega : n+(m-1) = n+m-1)]
    have h := hF.mul_mem p n (s-r+1) (m-1) x u hxF hu
    simpa only [show p+(s-r+1)=p+s-r+1 by omega] using h
  have hdv : K.d (n+m-1) (n+m) v =
      sign (R := R) n • c + B.mul n m x (K.d (m-1) m u) := by
    dsimp only [v]
    have h := d_mul_cast_at B rfl (by omega : (m-1)+1 = m)
      (by omega : n+m-1+1 = n+m) (by omega : n+(m-1) = n+m-1) x u
    simp only [degreeCast_rfl] at h
    rw [map_smul, h, smul_add, smul_smul, sign_sq, one_smul]
  have hdvF : K.d (n+m-1) (n+m) v ∈ carrier (F.piece (p+s) (n+m)) := by
    rw [hdv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (piece_mem_mono F (by omega) hc))
      (hF.mul_mem p n s m x _ hxF hdu)
  apply (mem_denominator_iff F r (p+s) (n+m) _ (mul_mem_almost B F hF r p n s m x y hx hy)).2
  refine ⟨v, hv, hdvF, ?_⟩
  have hxy : B.mul n m x (y - K.d (m-1) m u) ∈ carrier (F.piece (p+s+1) (n+m)) := by
    have h := hF.mul_mem p n (s+1) m x _ hxF hyu
    simpa only [show p+(s+1) = p+s+1 by omega] using h
  have heq : B.mul n m x y - K.d (n+m-1) (n+m) v =
      B.mul n m x (y - K.d (m-1) m u) - sign (R := R) n • c := by
    rw [hdv, map_sub]
    abel
  rw [heq]
  exact Submodule.sub_mem _ hxy (Submodule.smul_mem _ _ hc)

end Denominator

section PageProducts
variable {K : CochainComplex (ModuleCat.{v} R) ℤ}
variable (B : Algebra K) (F : Filtration K) (hF : Compatible B F) (D : F03Specs.PageData F)
open FilteredPage

/-- Product of almost cycles followed by the target page projection. -/
def representativeMul (r p n s m : ℤ) :=
  (almostMul B F hF r p n s m).compr₂
    (toPage F r (p+s) (n+m) (D.containment r (p+s) (n+m))).hom

/-- The left kernel condition for bilinear descent to pages. -/
theorem representativeMul_left (r p n s m : ℤ) :
    (toPage F r p n (D.containment r p n)).hom.ker ≤
      (representativeMul B F hF D r p n s m).ker := by
  intro x hx
  ext y
  apply (toPage_eq_zero_iff F r (p+s) (n+m) _ _).2
  rw [almostMul_arrow]
  exact mul_denominator_left B F hF r p n s m _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    ((toPage_eq_zero_iff F r p n _ x).1 hx)

/-- The right kernel condition for bilinear descent to pages. -/
theorem representativeMul_right (r p n s m : ℤ) :
    (toPage F r s m (D.containment r s m)).hom.ker ≤
      (representativeMul B F hF D r p n s m).flip.ker := by
  intro y hy
  ext x
  apply (toPage_eq_zero_iff F r (p+s) (n+m) _ _).2
  rw [almostMul_arrow]
  exact mul_denominator_right B F hF r p n s m _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    ((toPage_eq_zero_iff F r s m _ y).1 hy)

/-- The product on the fixed categorical pages, for every integer page index. -/
def pageMul (r p n s m : ℤ) : pageObject F D r p n →ₗ[R]
    pageObject F D r s m →ₗ[R] pageObject F D r (p+s) (n+m) :=
  descendBilinear (toPage F r p n (D.containment r p n)).hom
    (toPage F r s m (D.containment r s m)).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    (representativeMul B F hF D r p n s m)
    (representativeMul_left B F hF D r p n s m)
    (representativeMul_right B F hF D r p n s m)

@[simp] theorem pageMul_toPage (r p n s m : ℤ)
    (x : (almost F r p n : ModuleCat R)) (y : (almost F r s m : ModuleCat R)) :
    pageMul B F hF D r p n s m (toPage F r p n (D.containment r p n) x)
      (toPage F r s m (D.containment r s m) y) =
      toPage F r (p+s) (n+m) (D.containment r (p+s) (n+m))
        (almostMul B F hF r p n s m x y) := by
  exact descendBilinear_apply _ _ _ _ _ _ _ x y

/-- Canonical transport of an almost-cycle representative. -/
abbrev almostReindex (r : ℤ) {p n s m : ℤ} (hp : p = s) (hn : n = m) :
    (almost F r p n : ModuleCat R) →ₗ[R] (almost F r s m : ModuleCat R) :=
  (eqToHom (by subst s; subst m; rfl :
    (almost F r p n : ModuleCat R) = (almost F r s m : ModuleCat R))).hom

@[simp] theorem almostReindex_arrow (r : ℤ) {p n s m : ℤ} (hp : p = s) (hn : n = m)
    (x : (almost F r p n : ModuleCat R)) :
    (almost F r s m).arrow (almostReindex F r hp hn x) =
      degreeCast hn ((almost F r p n).arrow x) := by
  subst s; subst m; rfl

@[simp] theorem reindex_toPage (r : ℤ) {p n s m : ℤ} (hp : p = s) (hn : n = m)
    (x : (almost F r p n : ModuleCat R)) :
    reindex (pageObject F D r) hp hn (toPage F r p n (D.containment r p n) x) =
      toPage F r s m (D.containment r s m) (almostReindex F r hp hn x) := by
  subst s; subst m; rfl

/-- Two products of three numerator representatives agree after reindexing. -/
theorem almostMul_assoc (r p n s m t l : ℤ)
    (x : (almost F r p n : ModuleCat R)) (y : (almost F r s m : ModuleCat R))
    (z : (almost F r t l : ModuleCat R)) :
    almostReindex F r (by omega : (p+s)+t = p+(s+t))
      (by omega : (n+m)+l = n+(m+l))
      (almostMul B F hF r (p+s) (n+m) t l (almostMul B F hF r p n s m x y) z) =
      almostMul B F hF r p n (s+t) (m+l) x (almostMul B F hF r s m t l y z) := by
  apply (ModuleCat.mono_iff_injective (almost F r (p+(s+t)) (n+(m+l))).arrow).1 inferInstance
  simp only [almostReindex_arrow, almostMul_arrow]
  have h := B.assoc n m l ((almost F r p n).arrow x)
    ((almost F r s m).arrow y) ((almost F r t l).arrow z)
  exact eq_of_heq ((degreeCast_heq _ _).trans h)

theorem reindex_heq (E : ℤ → ℤ → ModuleCat.{v} R) {p n s m : ℤ}
    (hp : p = s) (hn : n = m) (x : E p n) : HEq (reindex E hp hn x) x := by
  subst s; subst m; rfl

/-- Associativity on the actual quotients. -/
theorem pageMul_assoc (r p n s m t l : ℤ)
    (x : pageObject F D r p n) (y : pageObject F D r s m) (z : pageObject F D r t l) :
    HEq (pageMul B F hF D r (p+s) (n+m) t l (pageMul B F hF D r p n s m x y) z)
      (pageMul B F hF D r p n (s+t) (m+l) x (pageMul B F hF D r s m t l y z)) := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r p n (D.containment r p n))).1 inferInstance x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r s m (D.containment r s m))).1 inferInstance y
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r t l (D.containment r t l))).1 inferInstance z
  simp only [pageMul_toPage]
  have h := congrArg (toPage F r (p+(s+t)) (n+(m+l)) (D.containment r _ _))
    (almostMul_assoc B F hF r p n s m t l x y z)
  rw [← reindex_toPage] at h
  exact (reindex_heq _ _ _ _).symm.trans (heq_of_eq h)

@[simp] theorem restriction_arrow_apply (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (x : (almost F r p n : ModuleCat R)) :
    (almost F r (p+r) (n+1)).arrow (D.restriction r hr p n x) =
      K.d n (n+1) ((almost F r p n).arrow x) :=
  ConcreteCategory.congr_hom (D.restriction_arrow r hr p n) x

@[simp] theorem differential_toPage (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (x : (almost F r p n : ModuleCat R)) :
    D.differential r hr p n (toPage F r p n (D.containment r p n) x) =
      toPage F r (p+r) (n+1) (D.containment r (p+r) (n+1)) (D.restriction r hr p n x) :=
  ConcreteCategory.congr_hom (D.representative_formula r hr p n) x

/-- The original total-degree Leibniz sign descends to every page. -/
theorem pageMul_leibniz (r : ℤ) (hr : 0 ≤ r) (p n s m : ℤ)
    (x : pageObject F D r p n) (y : pageObject F D r s m) :
    D.differential r hr (p+s) (n+m) (pageMul B F hF D r p n s m x y) =
      reindex (pageObject F D r) (by omega : (p+r)+s = (p+s)+r)
        (by omega : (n+1)+m = (n+m)+1)
        (pageMul B F hF D r (p+r) (n+1) s m (D.differential r hr p n x) y) +
      sign (R := R) n •
        reindex (pageObject F D r) (by omega : p+(s+r) = (p+s)+r)
          (by omega : n+(m+1) = (n+m)+1)
          (pageMul B F hF D r p n (s+r) (m+1) x (D.differential r hr s m y)) := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r p n (D.containment r p n))).1 inferInstance x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r s m (D.containment r s m))).1 inferInstance y
  simp only [pageMul_toPage, differential_toPage, reindex_toPage]
  rw [← map_smul, ← map_add]
  congr 1
  apply (ModuleCat.mono_iff_injective (almost F r ((p+s)+r) (n+m+1)).arrow).1 inferInstance
  simp only [map_add, map_smul, almostReindex_arrow, almostMul_arrow, restriction_arrow_apply]
  exact B.leibniz n m _ _

/-- The closed algebra unit is an almost cycle on every page. -/
def unitAlmost (U : Unit B) (hU : U.one ∈ carrier (F.piece 0 0)) (r : ℤ) :
    (almost F r 0 0 : ModuleCat R) :=
  (carrierEquiv _).symm ⟨U.one, (mem_almost_iff_at F r 0 0 1 (by omega) U.one).2
    ⟨hU, by rw [U.closed]; exact Submodule.zero_mem _⟩⟩

@[simp] theorem unitAlmost_arrow (U : Unit B) (hU : U.one ∈ carrier (F.piece 0 0)) (r : ℤ) :
    (almost F r 0 0).arrow (unitAlmost B F U hU r) = U.one :=
  arrow_carrierEquiv_symm _ _

/-- The class of the optional unit is a left identity. -/
theorem pageMul_unit_left (U : Unit B) (hU : U.one ∈ carrier (F.piece 0 0)) (r p n : ℤ)
    (x : pageObject F D r p n) :
    HEq (pageMul B F hF D r 0 0 p n
      (toPage F r 0 0 (D.containment r 0 0) (unitAlmost B F U hU r)) x) x := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r p n (D.containment r p n))).1 inferInstance x
  rw [pageMul_toPage]
  have h : almostReindex F r (by omega : 0+p=p) (by omega : 0+n=n)
      (almostMul B F hF r 0 0 p n (unitAlmost B F U hU r) x) = x := by
    apply (ModuleCat.mono_iff_injective (almost F r p n).arrow).1 inferInstance
    simp only [almostReindex_arrow, almostMul_arrow, unitAlmost_arrow]
    exact eq_of_heq ((degreeCast_heq _ _).trans (U.left n _))
  have hh := congrArg (toPage F r p n (D.containment r p n)) h
  rw [← reindex_toPage] at hh
  exact (reindex_heq _ _ _ _).symm.trans (heq_of_eq hh)

/-- The class of the optional unit is a right identity. -/
theorem pageMul_unit_right (U : Unit B) (hU : U.one ∈ carrier (F.piece 0 0)) (r p n : ℤ)
    (x : pageObject F D r p n) :
    HEq (pageMul B F hF D r p n 0 0 x
      (toPage F r 0 0 (D.containment r 0 0) (unitAlmost B F U hU r))) x := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
    (toPage F r p n (D.containment r p n))).1 inferInstance x
  rw [pageMul_toPage]
  have h : almostReindex F r (by omega : p+0=p) (by omega : n+0=n)
      (almostMul B F hF r p n 0 0 x (unitAlmost B F U hU r)) = x := by
    apply (ModuleCat.mono_iff_injective (almost F r p n).arrow).1 inferInstance
    simp only [almostReindex_arrow, almostMul_arrow, unitAlmost_arrow]
    exact eq_of_heq ((degreeCast_heq _ _).trans (U.right n _))
  have hh := congrArg (toPage F r p n (D.containment r p n)) h
  rw [← reindex_toPage] at hh
  exact (reindex_heq _ _ _ _).symm.trans (heq_of_eq hh)

/-- Associative, unital when appropriate, multiplicative pages with derivations. -/
def products : Products B F D where
  mul r _ := pageMul B F hF D r
  representative r _ p n s m x y :=
    ⟨almostMul B F hF r p n s m x y, almostMul_arrow B F hF r p n s m x y,
      pageMul_toPage B F hF D r p n s m x y⟩
  assoc r _ := pageMul_assoc B F hF D r
  leibniz := pageMul_leibniz B F hF D
  unit U hU r _ := ⟨unitAlmost B F U hU r, unitAlmost_arrow B F U hU r,
    pageMul_unit_left B F hF D U hU r, pageMul_unit_right B F hF D U hU r⟩

end PageProducts

section NextProducts
variable {K : CochainComplex (ModuleCat.{v} R) ℤ}
variable (B : Algebra K) (F : Filtration K) (hF : Compatible B F) (D : F03Specs.PageData F)
open FilteredPage PageCohomology

variable (C : PageCohomology.Data F D)

abbrev nextCyclesMap (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :=
  (shortComplex F D r hr p n).liftCycles
    (nextRepresentative F D r (p+r) (n+1)) (C.next_cycle r hr p n)

instance nextCyclesMap_epi (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    Epi (nextCyclesMap F D C r hr p n) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro T z
  obtain ⟨T', e, he, w, hw⟩ := PageCohomology.lift_next_cycle F D r hr (p+r) (n+1)
    (z ≫ (shortComplex F D r hr p n).iCycles) (by
      change (z ≫ (shortComplex F D r hr p n).iCycles) ≫ (shortComplex F D r hr p n).g = 0
      rw [Category.assoc, ShortComplex.iCycles_g, comp_zero])
  refine ⟨T', e, he, w, ?_⟩
  apply (cancel_mono (shortComplex F D r hr p n).iCycles).1
  change (e ≫ z) ≫ (shortComplex F D r hr p n).iCycles =
    (w ≫ (shortComplex F D r hr p n).liftCycles
      (nextRepresentative F D r (p+r) (n+1)) (C.next_cycle r hr p n)) ≫
        (shortComplex F D r hr p n).iCycles
  rw [Category.assoc w]
  erw [ShortComplex.liftCycles_i]
  exact hw

@[simp] theorem nextCyclesMap_i (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (x : (almost F (r+1) (p+r) (n+1) : ModuleCat R)) :
    (shortComplex F D r hr p n).iCycles (nextCyclesMap F D C r hr p n x) =
      nextRepresentative F D r (p+r) (n+1) x :=
  ConcreteCategory.congr_hom (ShortComplex.liftCycles_i _ _ _) x

@[simp] theorem nextCyclesMap_homologyπ (r : ℤ) (hr : 0 ≤ r) (p n : ℤ)
    (x : (almost F (r+1) (p+r) (n+1) : ModuleCat R)) :
    (shortComplex F D r hr p n).homologyπ (nextCyclesMap F D C r hr p n x) =
      (C.nextIso r hr p n).hom (toPage F (r+1) (p+r) (n+1) (D.containment _ _ _) x) :=
  (ConcreteCategory.congr_hom (C.nextIso_formula r hr p n) x).symm

@[simp] theorem reindex_nextRepresentative (r : ℤ) {p n s m : ℤ} (hp : p = s) (hn : n = m)
    (x : (almost F (r+1) p n : ModuleCat R)) :
    reindex (pageObject F D r) hp hn (nextRepresentative F D r p n x) =
      nextRepresentative F D r s m (almostReindex F (r+1) hp hn x) := by
  subst s; subst m; rfl

@[simp] theorem nextRepresentative_mul (r p n s m : ℤ)
    (x : (almost F (r+1) p n : ModuleCat R))
    (y : (almost F (r+1) s m : ModuleCat R)) :
    pageMul B F hF D r p n s m (nextRepresentative F D r p n x)
      (nextRepresentative F D r s m y) =
      nextRepresentative F D r (p+s) (n+m) (almostMul B F hF (r+1) p n s m x y) := by
  change pageMul B F hF D r p n s m
      (toPage F r p n (D.containment _ _ _) (Subobject.ofLE _ _ (almost_succ_le F r p n) x))
      (toPage F r s m (D.containment _ _ _) (Subobject.ofLE _ _ (almost_succ_le F r s m) y)) = _
  rw [pageMul_toPage]
  change toPage F r (p+s) (n+m) (D.containment _ _ _)
    (almostMul B F hF r p n s m (Subobject.ofLE _ _ (almost_succ_le F r p n) x)
      (Subobject.ofLE _ _ (almost_succ_le F r s m) y)) =
    toPage F r (p+s) (n+m) (D.containment _ _ _)
      (Subobject.ofLE _ _ (almost_succ_le F r (p+s) (n+m))
        (almostMul B F hF (r+1) p n s m x y))
  congr 1
  apply (ModuleCat.mono_iff_injective (almost F r (p+s) (n+m)).arrow).1 inferInstance
  simp only [almostMul_arrow, ← ConcreteCategory.comp_apply, Subobject.ofLE_arrow]

/-- The next-page product transported through the specified canonical isomorphisms. -/
def nextMul (r : ℤ) (hr : 0 ≤ r) (p n s m : ℤ) :
    (shortComplex F D r hr p n).homology →ₗ[R]
    (shortComplex F D r hr s m).homology →ₗ[R]
    (shortComplex F D r hr (p+s+r) (n+m+1)).homology :=
  ((pageMul B F hF D (r+1) (p+r) (n+1) (s+r) (m+1)).compr₂
    ((C.nextIso r hr (p+s+r) (n+m+1)).hom.hom.comp
      (reindex (pageObject F D (r+1)) (by omega) (by omega)))).compl₁₂
        (C.nextIso r hr p n).inv.hom (C.nextIso r hr s m).inv.hom

@[simp] theorem nextMul_nextIso (r : ℤ) (hr : 0 ≤ r) (p n s m : ℤ)
    (x : pageObject F D (r+1) (p+r) (n+1))
    (y : pageObject F D (r+1) (s+r) (m+1)) :
    nextMul B F hF D C r hr p n s m ((C.nextIso r hr p n).hom x)
      ((C.nextIso r hr s m).hom y) =
      (C.nextIso r hr (p+s+r) (n+m+1)).hom
        (reindex (pageObject F D (r+1)) (by omega) (by omega)
          (pageMul B F hF D (r+1) (p+r) (n+1) (s+r) (m+1) x y)) := by
  simp [nextMul, ← ConcreteCategory.comp_apply]

theorem nextMul_cycle_formula (r : ℤ) (hr : 0 ≤ r) (p n s m : ℤ)
    (x : (shortComplex F D r hr p n).cycles)
    (y : (shortComplex F D r hr s m).cycles) :
    ∃ z : (shortComplex F D r hr (p+s+r) (n+m+1)).cycles,
      HEq ((shortComplex F D r hr (p+s+r) (n+m+1)).iCycles z)
        (pageMul B F hF D r (p+r) (n+1) (s+r) (m+1)
          ((shortComplex F D r hr p n).iCycles x)
          ((shortComplex F D r hr s m).iCycles y)) ∧
      nextMul B F hF D C r hr p n s m
        ((shortComplex F D r hr p n).homologyπ x)
        ((shortComplex F D r hr s m).homologyπ y) =
          (shortComplex F D r hr (p+s+r) (n+m+1)).homologyπ z := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (nextCyclesMap F D C r hr p n)).1
    inferInstance x
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (nextCyclesMap F D C r hr s m)).1
    inferInstance y
  let z := nextCyclesMap F D C r hr (p+s+r) (n+m+1)
    (almostReindex F (r+1) (by omega) (by omega)
      (almostMul B F hF (r+1) (p+r) (n+1) (s+r) (m+1) a b))
  refine ⟨z, ?_, ?_⟩
  · dsimp only [z]
    simp only [nextCyclesMap_i]
    have h := reindex_nextRepresentative F D r
      (by omega : (p+r)+(s+r) = (p+s+r)+r)
      (by omega : (n+1)+(m+1) = (n+m+1)+1)
      (almostMul B F hF (r+1) (p+r) (n+1) (s+r) (m+1) a b)
    rw [← nextRepresentative_mul B F hF D] at h
    exact (heq_of_eq h.symm).trans (reindex_heq _ _ _ _)
  · dsimp only [z]
    simp only [nextCyclesMap_homologyπ, nextMul_nextIso, pageMul_toPage, reindex_toPage]

/-- Products on the canonical next page agree with products on all current-page cycles. -/
def nextCompatibility : NextCompatibility B F D (products B F hF D) C where
  mul := nextMul B F hF D C
  cycle_formula := nextMul_cycle_formula B F hF D C
  next_formula := nextMul_nextIso B F hF D C
end NextProducts

section CohomologyProducts
variable {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- Concrete constructor for actual cycles. -/
def cyclesMk (n : ℤ) (x : K.X n) (hx : K.d n (n+1) x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x, by change K.d n ((ComplexShape.up ℤ).next n) x = 0; rw [CochainComplex.next]; exact hx⟩

@[simp] theorem iCycles_cyclesMk (n : ℤ) (x : K.X n) (hx : K.d n (n+1) x = 0) :
    K.iCycles n (cyclesMk n x hx) = x := by
  exact ConcreteCategory.congr_hom (K.sc n).moduleCatCyclesIso_inv_iCycles ⟨x, by change K.d n ((ComplexShape.up ℤ).next n) x = 0; rw [CochainComplex.next]; exact hx⟩

@[simp] theorem cycles_closed (n : ℤ) (x : K.cycles n) :
    K.d n (n+1) (K.iCycles n x) = 0 :=
  (ConcreteCategory.congr_hom (K.iCycles_d n (n+1)) x).trans (by simp)

theorem homologyπ_eq_zero_iff_boundary (n : ℤ) (x : K.cycles n) :
    K.homologyπ n x = 0 ↔ ∃ y : K.X (n-1), K.d (n-1) n y = K.iCycles n x := by
  let S := ShortComplex.mk (K.toCycles (n-1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n-1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel (K.homologyIsCokernel (n-1) n (by simp))
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff.mp hS) x hx
    refine ⟨y, ?_⟩
    simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using
      congrArg (K.iCycles n) (show K.toCycles (n-1) n y = x from hy)
  · rintro ⟨y, hy⟩
    have h : K.toCycles (n-1) n y = x := by
      apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
      simpa only [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i] using hy
    rw [← h, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    rfl

@[simp] theorem mem_carrier_kernel {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M) :
    x ∈ carrier (kernelSubobject f) ↔ f x = 0 := by
  rw [mem_carrier_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact (ConcreteCategory.congr_hom (kernelSubobject_arrow_comp f) a).trans (by simp)
  · intro hx
    refine ⟨(kernelSubobjectIso f).inv ((ModuleCat.kernelIsoKer f).inv ⟨x, hx⟩), ?_⟩
    rw [← ConcreteCategory.comp_apply, kernelSubobject_arrow',
      ← ConcreteCategory.comp_apply, ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl

open FiniteFiltrationConvergence
variable (F : Filtration K)

def closedToCycles (p n : ℤ) : (closed F p n : ModuleCat R) ⟶ K.cycles n :=
  K.liftCycles (closed F p n).arrow (n+1) (by simp) (closed_d F p n)

@[simp] theorem closedToCycles_i (p n : ℤ) (x : (closed F p n : ModuleCat R)) :
    K.iCycles n (closedToCycles F p n x) = (closed F p n).arrow x :=
  ConcreteCategory.congr_hom (K.liftCycles_i _ _ _ _) x

@[simp] theorem closedClass_arrow_apply (p n : ℤ) (x : (closed F p n : ModuleCat R)) :
    (cohomologyPiece F p n).arrow (closedClass F p n x) =
      K.homologyπ n (closedToCycles F p n x) :=
  ConcreteCategory.congr_hom (closedClass_arrow F p n) x

variable (B : Algebra K)

theorem mul_closed (n m : ℤ) (x : K.cycles n) (y : K.cycles m) :
    K.d (n+m) (n+m+1) (B.mul n m (K.iCycles n x) (K.iCycles m y)) = 0 := by
  rw [B.leibniz, cycles_closed, cycles_closed]
  simp

def cyclesMul (n m : ℤ) : K.cycles n →ₗ[R] K.cycles m →ₗ[R] K.cycles (n+m) where
  toFun x :=
    { toFun := fun y => cyclesMk (n+m) (B.mul n m (K.iCycles n x) (K.iCycles m y))
        (mul_closed B n m x y)
      map_add' y z := by
        apply (ModuleCat.mono_iff_injective (K.iCycles (n+m))).1 inferInstance
        simp only [map_add, iCycles_cyclesMk]
      map_smul' a y := by
        apply (ModuleCat.mono_iff_injective (K.iCycles (n+m))).1 inferInstance
        simp only [map_smul, iCycles_cyclesMk, RingHom.id_apply] }
  map_add' x y := by
    ext z
    apply (ModuleCat.mono_iff_injective (K.iCycles (n+m))).1 inferInstance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      map_add, iCycles_cyclesMk]
  map_smul' a x := by
    ext y
    apply (ModuleCat.mono_iff_injective (K.iCycles (n+m))).1 inferInstance
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      map_smul, iCycles_cyclesMk, RingHom.id_apply]

@[simp] theorem cyclesMul_i (n m : ℤ) (x : K.cycles n) (y : K.cycles m) :
    K.iCycles (n+m) (cyclesMul B n m x y) = B.mul n m (K.iCycles n x) (K.iCycles m y) :=
  iCycles_cyclesMk _ _ (mul_closed B n m x y)

theorem cyclesMul_boundary_left (n m : ℤ) (x : K.cycles n) (y : K.cycles m)
    (hx : K.homologyπ n x = 0) : K.homologyπ (n+m) (cyclesMul B n m x y) = 0 := by
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff_boundary n x).1 hx
  apply (homologyπ_eq_zero_iff_boundary (n+m) _).2
  refine ⟨degreeCast (by omega : (n-1)+m = (n+m)-1)
    (B.mul (n-1) m u (K.iCycles m y)), ?_⟩
  rw [d_mul_cast_at B (by omega : (n-1)+1=n) rfl
    (by omega : (n+m-1)+1=n+m)]
  simp only [cycles_closed, map_zero, degreeCast_rfl, smul_zero, add_zero, hu, cyclesMul_i]

theorem cyclesMul_boundary_right (n m : ℤ) (x : K.cycles n) (y : K.cycles m)
    (hy : K.homologyπ m y = 0) : K.homologyπ (n+m) (cyclesMul B n m x y) = 0 := by
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff_boundary m y).1 hy
  apply (homologyπ_eq_zero_iff_boundary (n+m) _).2
  refine ⟨sign (R := R) n • degreeCast (by omega : n+(m-1) = (n+m)-1)
    (B.mul n (m-1) (K.iCycles n x) u), ?_⟩
  rw [map_smul, d_mul_cast_at B rfl (by omega : (m-1)+1=m)
    (by omega : (n+m-1)+1=n+m)]
  simp only [cycles_closed, map_zero, LinearMap.zero_apply, degreeCast_rfl,
    zero_add, hu, smul_smul, sign_sq, one_smul, cyclesMul_i]

def cohomologyMul (n m : ℤ) : K.homology n →ₗ[R] K.homology m →ₗ[R] K.homology (n+m) :=
  descendBilinear (K.homologyπ n).hom (K.homologyπ m).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ((cyclesMul B n m).compr₂ (K.homologyπ (n+m)).hom)
    (by
      intro x hx
      apply LinearMap.ext
      intro y
      exact cyclesMul_boundary_left B n m x y hx)
    (by
      intro y hy
      apply LinearMap.ext
      intro x
      exact cyclesMul_boundary_right B n m x y hy)

@[simp] theorem cohomologyMul_cycles (n m : ℤ) (x : K.cycles n) (y : K.cycles m) :
    cohomologyMul B n m (K.homologyπ n x) (K.homologyπ m y) =
      K.homologyπ (n+m) (cyclesMul B n m x y) := by
  exact descendBilinear_apply _ _ _ _ _ _ _ x y

variable (hF : Compatible B F)

include hF in
theorem mul_mem_closed (p n s m : ℤ) (x : K.X n) (y : K.X m)
    (hx : x ∈ carrier (closed F p n)) (hy : y ∈ carrier (closed F s m)) :
    B.mul n m x y ∈ carrier (closed F (p+s) (n+m)) := by
  obtain ⟨hx, hdx⟩ := (mem_carrier_inf _ _ _).1 hx
  obtain ⟨hy, hdy⟩ := (mem_carrier_inf _ _ _).1 hy
  apply (mem_carrier_inf _ _ _).2
  refine ⟨hF.mul_mem p n s m x y hx hy, ?_⟩
  rw [mem_carrier_kernel, B.leibniz, (mem_carrier_kernel _ _).1 hdx,
    (mem_carrier_kernel _ _).1 hdy]
  simp

def closedMul (p n s m : ℤ) : (closed F p n : ModuleCat R) →ₗ[R]
    (closed F s m : ModuleCat R) →ₗ[R] (closed F (p+s) (n+m) : ModuleCat R) :=
  restrictBilinear _ _ _ (B.mul n m) (mul_mem_closed F B hF p n s m)

@[simp] theorem closedMul_arrow (p n s m : ℤ)
    (x : (closed F p n : ModuleCat R)) (y : (closed F s m : ModuleCat R)) :
    (closed F (p+s) (n+m)).arrow (closedMul F B hF p n s m x y) =
      B.mul n m ((closed F p n).arrow x) ((closed F s m).arrow y) :=
  restrictBilinear_arrow _ _ _ _ _ _ _

@[simp] theorem cohomologyMul_closedClass (p n s m : ℤ)
    (x : (closed F p n : ModuleCat R)) (y : (closed F s m : ModuleCat R)) :
    cohomologyMul B n m ((cohomologyPiece F p n).arrow (closedClass F p n x))
      ((cohomologyPiece F s m).arrow (closedClass F s m y)) =
    (cohomologyPiece F (p+s) (n+m)).arrow
      (closedClass F (p+s) (n+m) (closedMul F B hF p n s m x y)) := by
  simp only [closedClass_arrow_apply, cohomologyMul_cycles]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles (n+m))).1 inferInstance
  simp only [cyclesMul_i, closedToCycles_i, closedMul_arrow]

include hF in
theorem mul_mem_cohomologyPiece (p n s m : ℤ) (x : K.homology n) (y : K.homology m)
    (hx : x ∈ carrier (cohomologyPiece F p n))
    (hy : y ∈ carrier (cohomologyPiece F s m)) :
    cohomologyMul B n m x y ∈ carrier (cohomologyPiece F (p+s) (n+m)) := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (closedClass F p n)).1 inferInstance x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (closedClass F s m)).1 inferInstance y
  refine ⟨closedClass F (p+s) (n+m) (closedMul F B hF p n s m x y), ?_⟩
  exact (cohomologyMul_closedClass F B hF p n s m x y).symm

def cohomologyFilteredMul (p n s m : ℤ) : (cohomologyPiece F p n : ModuleCat R) →ₗ[R]
    (cohomologyPiece F s m : ModuleCat R) →ₗ[R]
      (cohomologyPiece F (p+s) (n+m) : ModuleCat R) :=
  restrictBilinear _ _ _ (cohomologyMul B n m) (mul_mem_cohomologyPiece F B hF p n s m)

@[simp] theorem cohomologyFilteredMul_arrow (p n s m : ℤ)
    (x : (cohomologyPiece F p n : ModuleCat R)) (y : (cohomologyPiece F s m : ModuleCat R)) :
    (cohomologyPiece F (p+s) (n+m)).arrow (cohomologyFilteredMul F B hF p n s m x y) =
      cohomologyMul B n m ((cohomologyPiece F p n).arrow x) ((cohomologyPiece F s m).arrow y) :=
  restrictBilinear_arrow _ _ _ _ _ _ _

theorem cokernel_π_ofLE_eq_zero_iff {M : ModuleCat.{v} R} (S T : Subobject M)
    (h : S ≤ T) (x : (T : ModuleCat R)) :
    cokernel.π (Subobject.ofLE S T h) x = 0 ↔ T.arrow x ∈ carrier S := by
  rw [cokernel_π_eq_zero_iff, mem_carrier_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← Subobject.ofLE_arrow h, ConcreteCategory.comp_apply, ha]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (ModuleCat.mono_iff_injective T.arrow).1 inferInstance
    rw [← ConcreteCategory.comp_apply, Subobject.ofLE_arrow]
    exact ha

abbrev cohomologyGradedπ (p n : ℤ) :
    (cohomologyPiece F p n : ModuleCat R) ⟶ gradedCohomology F p n :=
  cokernel.π (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))

def gradedRepresentativeMul (p n s m : ℤ) :=
  (cohomologyFilteredMul F B hF p n s m).compr₂ (cohomologyGradedπ F (p+s) (n+m)).hom

theorem gradedRepresentativeMul_left (p n s m : ℤ) :
    (cohomologyGradedπ F p n).hom.ker ≤ (gradedRepresentativeMul F B hF p n s m).ker := by
  intro x hx
  ext y
  change cohomologyGradedπ F (p+s) (n+m) (cohomologyFilteredMul F B hF p n s m x y) = 0
  apply (cokernel_π_ofLE_eq_zero_iff _ _ _ _).2
  rw [cohomologyFilteredMul_arrow]
  have h := mul_mem_cohomologyPiece F B hF (p+1) n s m
    ((cohomologyPiece F p n).arrow x) ((cohomologyPiece F s m).arrow y)
    ((cokernel_π_ofLE_eq_zero_iff _ _ _ _).1 hx) ⟨y, rfl⟩
  simpa only [show (p+1)+s = (p+s)+1 by omega] using h

theorem gradedRepresentativeMul_right (p n s m : ℤ) :
    (cohomologyGradedπ F s m).hom.ker ≤ (gradedRepresentativeMul F B hF p n s m).flip.ker := by
  intro y hy
  ext x
  change cohomologyGradedπ F (p+s) (n+m) (cohomologyFilteredMul F B hF p n s m x y) = 0
  apply (cokernel_π_ofLE_eq_zero_iff _ _ _ _).2
  rw [cohomologyFilteredMul_arrow]
  have h := mul_mem_cohomologyPiece F B hF p n (s+1) m
    ((cohomologyPiece F p n).arrow x) ((cohomologyPiece F s m).arrow y)
    ⟨x, rfl⟩ ((cokernel_π_ofLE_eq_zero_iff _ _ _ _).1 hy)
  simpa only [show p+(s+1) = (p+s)+1 by omega] using h

def cohomologyGradedMul (p n s m : ℤ) : (gradedCohomology F p n : ModuleCat R) →ₗ[R]
    (gradedCohomology F s m : ModuleCat R) →ₗ[R]
      (gradedCohomology F (p+s) (n+m) : ModuleCat R) :=
  descendBilinear (cohomologyGradedπ F p n).hom (cohomologyGradedπ F s m).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    (gradedRepresentativeMul F B hF p n s m)
    (gradedRepresentativeMul_left F B hF p n s m)
    (gradedRepresentativeMul_right F B hF p n s m)

@[simp] theorem cohomologyGradedMul_projection (p n s m : ℤ)
    (x : (cohomologyPiece F p n : ModuleCat R)) (y : (cohomologyPiece F s m : ModuleCat R)) :
    cohomologyGradedMul F B hF p n s m (cohomologyGradedπ F p n x) (cohomologyGradedπ F s m y) =
      cohomologyGradedπ F (p+s) (n+m) (cohomologyFilteredMul F B hF p n s m x y) := by
  exact descendBilinear_apply _ _ _ _ _ _ _ x y

/-- Cohomology multiplication, the actual image filtration and its graded product. -/
def cohomologyProducts : CohomologyProducts B F where
  mul := cohomologyMul B
  representative n m x y := ⟨cyclesMul B n m x y, cyclesMul_i B n m x y,
    cohomologyMul_cycles B n m x y⟩
  filtered p n s m x y := ⟨cohomologyFilteredMul F B hF p n s m x y,
    cohomologyFilteredMul_arrow F B hF p n s m x y⟩
  gradedMul := cohomologyGradedMul F B hF
  graded_formula p n s m x y z hz := by
    rw [cohomologyGradedMul_projection]
    congr 1
    apply (ModuleCat.mono_iff_injective (cohomologyPiece F (p+s) (n+m)).arrow).1 inferInstance
    exact (cohomologyFilteredMul_arrow F B hF p n s m x y).trans hz.symm
end CohomologyProducts

section StableProducts
variable {K : CochainComplex (ModuleCat.{v} R) ℤ}
open FilteredPage FiniteFiltrationConvergence

private theorem stableCohomology_formula (B : Algebra K) (F : Filtration K)
    (hF : Compatible B F) (H : CohomologyProducts B F)
    (p n s m : ℤ) (x : (closed F p n : ModuleCat R))
    (y : (closed F s m : ModuleCat R)) :
    (cohomologyPiece F (p+s) (n+m)).arrow
      (closedClass F (p+s) (n+m) (closedMul F B hF p n s m x y)) =
      H.mul n m ((cohomologyPiece F p n).arrow (closedClass F p n x))
        ((cohomologyPiece F s m).arrow (closedClass F s m y)) := by
  simp only [closedClass_arrow_apply]
  obtain ⟨z, hz, hmul⟩ := H.representative n m (closedToCycles F p n x)
    (closedToCycles F s m y)
  rw [hmul]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.iCycles (n+m))).1 inferInstance
  simpa only [closedToCycles_i, closedMul_arrow] using hz.symm

private theorem stablePage_formula (B : Algebra K) (F : Filtration K)
    (hF : Compatible B F) (D : F03Specs.PageData F) (P : Products B F D)
    (r : ℤ) (hr : 0 ≤ r) (p n s m : ℤ)
    (x : (closed F p n : ModuleCat R)) (y : (closed F s m : ModuleCat R)) :
    P.mul r hr p n s m (closedToPage F D r p n x) (closedToPage F D r s m y) =
      closedToPage F D r (p+s) (n+m) (closedMul F B hF p n s m x y) := by
  obtain ⟨z, hz, hmul⟩ := P.representative r hr p n s m
    (Subobject.ofLE _ _ (closed_le_almost F r p n) x)
    (Subobject.ofLE _ _ (closed_le_almost F r s m) y)
  change P.mul r hr p n s m
      (toPage F r p n (D.containment r p n) (Subobject.ofLE _ _ (closed_le_almost F r p n) x))
      (toPage F r s m (D.containment r s m) (Subobject.ofLE _ _ (closed_le_almost F r s m) y)) = _
  rw [hmul]
  change toPage F r (p+s) (n+m) _ z =
    toPage F r (p+s) (n+m) _ (Subobject.ofLE _ _ (closed_le_almost F r (p+s) (n+m)) (closedMul F B hF p n s m x y))
  congr 1
  apply (ModuleCat.mono_iff_injective (almost F r (p+s) (n+m)).arrow).1 inferInstance
  rw [hz]
  simp only [← ConcreteCategory.comp_apply, Subobject.ofLE_arrow, closedMul_arrow]

/-- Products fixed by representatives commute with every canonical stable identification. -/
theorem stableCompatibilityOfRepresentatives (B : Algebra K) (F : Filtration K)
    (hF : Compatible B F) (D : F03Specs.PageData F) (P : Products B F D)
    (H : CohomologyProducts B F) : StableCompatibility B F D P H := by
  intro _ r hr p n s m hp hs _ L M N x y
  haveI := closedToPage_epi F D r p n hp.1
  haveI := closedToPage_epi F D r s m hs.1
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (closedToPage F D r p n)).1 inferInstance x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (closedToPage F D r s m)).1 inferInstance y
  have hL := ConcreteCategory.congr_hom L.representative_formula x
  have hM := ConcreteCategory.congr_hom M.representative_formula y
  have hN := ConcreteCategory.congr_hom N.representative_formula
    (closedMul F B hF p n s m x y)
  change L.iso.hom (closedToPage F D r p n x) = gradedClass F p n x at hL
  change M.iso.hom (closedToPage F D r s m y) = gradedClass F s m y at hM
  change N.iso.hom (closedToPage F D r (p+s) (n+m) _) = gradedClass F (p+s) (n+m) _ at hN
  rw [hL, hM, stablePage_formula B F hF D P, hN]
  exact H.graded_formula p n s m (closedClass F p n x) (closedClass F s m y)
    (closedClass F (p+s) (n+m) (closedMul F B hF p n s m x y))
    (stableCohomology_formula B F hF H p n s m x y)
end StableProducts

end MultiplicativePages

/-- Every page of a multiplicatively filtered DGA is an associative algebra
with the total-degree derivation law and the original optional unit. -/
theorem multiplicative_page_products : S06Specs.PageProducts.{u,v} := by
  intro R _ K B F hF D
  exact ⟨MultiplicativePages.products B F hF D⟩

/-- HA-S06: all multiplicative pages, canonical next-page products, and the
associated graded cohomology product under finite convergence. -/
theorem multiplicative_pages : S06Specs.FullStatement.{u,v} := by
  intro R _ K B F hF D C
  refine ⟨MultiplicativePages.products B F hF D,
    ⟨MultiplicativePages.nextCompatibility B F hF D C⟩,
    MultiplicativePages.cohomologyProducts F B hF, ?_⟩
  exact MultiplicativePages.stableCompatibilityOfRepresentatives B F hF D
    (MultiplicativePages.products B F hF D) (MultiplicativePages.cohomologyProducts F B hF)

end AdvancedHomologicalAlgebra
