import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DerivedExactCouples
import Mathlib.CategoryTheory.Abelian.Refinements

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
namespace AdvancedHomologicalAlgebra
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ExactCouple
variable {r : ℤ} (Q : ExactCouple C r)

/-- The image inclusion of i is a kernel of j. -/
def imageKernel (p a n : ℤ) (ha : a = p+r) :
    IsLimit (KernelFork.ofι (Q.inclusion p n)
      (image_ι_comp_eq_zero (Q.exact_ij p (p+1) a n rfl ha).zero)) :=
  (Q.exact_ij p (p+1) a n rfl ha).exact.isLimitImage'

/-- Lift through the image of i, using exactness at D. -/
def intoImage {A : C} (p a n : ℤ) (ha : a = p+r) (x : A ⟶ Q.D p n)
    (hx : x ≫ Q.j p a n ha = 0) : A ⟶ Q.derivedD p n :=
  (Q.imageKernel p a n ha).lift (KernelFork.ofι x hx)

@[reassoc (attr := simp)]
lemma intoImage_inclusion {A : C} (p a n : ℤ) (ha : a = p+r) (x : A ⟶ Q.D p n)
    (hx : x ≫ Q.j p a n ha = 0) :
    Q.intoImage p a n ha x hx ≫ Q.inclusion p n = x :=
  Fork.IsLimit.lift_ι _

/-- The map induced by i on its images. -/
def derivedI (p q n : ℤ) (hp : q = p+1) : Q.derivedD q n ⟶ Q.derivedD p n :=
  Q.intoImage p (p+r) n rfl (Q.inclusion q n ≫ Q.i p q n hp)
    (by rw [assoc, (Q.exact_ij p q (p+r) n hp rfl).zero, comp_zero])

@[reassoc (attr := simp)]
lemma derivedI_inclusion (p q n : ℤ) (hp : q = p+1) :
    Q.derivedI p q n hp ≫ Q.inclusion p n = Q.inclusion q n ≫ Q.i p q n hp := by
  simp [derivedI]

/-- j takes values in cycles. -/
def jCycles (a p n : ℤ) (ha : p = a+r) : Q.D a n ⟶ (Q.pageComplex p n).cycles :=
  (Q.pageComplex p n).liftCycles (Q.j a p n ha) (by
    dsimp [pageComplex, d]
    rw [← assoc, (Q.exact_jk _ _ _ _ _ _ _ _).zero, zero_comp])

@[reassoc (attr := simp)]
lemma jCycles_i (a p n : ℤ) (ha : p = a+r) :
    Q.jCycles a p n ha ≫ (Q.pageComplex p n).iCycles = Q.j a p n ha := by
  simp [jCycles]

/-- The quotient class of j of a representative. -/
def jClass (a p n : ℤ) (ha : p = a+r) : Q.D a n ⟶ Q.derivedE p n :=
  Q.jCycles a p n ha ≫ (Q.pageComplex p n).homologyπ

/-- Boundaries vanish in the page homology. -/
lemma k_jClass (a b p n m : ℤ) (hb : b = a+1) (hp : p = b+r) (hm : m = n+1) :
    Q.k a b n m hb hm ≫ Q.jClass b p m hp = 0 := by
  have ha : a = p-r-1 := by omega
  have hn : n = m-1 := by omega
  subst a n
  have hb' : b = p-r-1+1 := hb
  subst b
  dsimp [jClass, jCycles]
  rw [(Q.pageComplex p m).comp_liftCycles_assoc]
  apply (Q.pageComplex p m).liftCycles_homologyπ_eq_zero_of_boundary
    (Q.k (p-r-1) (p-r-1+1) (m-1) m rfl (by omega) ≫
      Q.j (p-r-1+1) p m (by omega)) (𝟙 _) (by simp [pageComplex, d])

/-- i onto its image is a cokernel of the preceding k. -/
def projectionCokernel (p n : ℤ) :
    IsColimit (CokernelCofork.ofπ (Q.projection p n)
      (comp_factorThruImage_eq_zero
        (Q.exact_ki p (p+1) (n-1) n rfl (by omega)).zero)) :=
  (Q.exact_ki p (p+1) (n-1) n rfl (by omega)).exact.isColimitImage

/-- j' is the descent of [j] along i onto its image. -/
def derivedJ (p q n : ℤ) (hq : q = p+(r+1)) : Q.derivedD p n ⟶ Q.derivedE q n :=
  (Q.projectionCokernel p n).desc
    (CokernelCofork.ofπ (Q.jClass (p+1) q n (by omega))
      (Q.k_jClass p (p+1) q (n-1) n rfl (by omega) (by omega)))

@[reassoc (attr := simp)]
lemma projection_derivedJ (p q n : ℤ) (hq : q = p+(r+1)) :
    Q.projection p n ≫ Q.derivedJ p q n hq = Q.jClass (p+1) q n (by omega) :=
  by
    dsimp only [derivedJ]
    exact Cofork.IsColimit.π_desc (Q.projectionCokernel p n)

/-- A cycle is taken by k into the kernel of j. -/
lemma cycles_k_j (p q a n m : ℤ) (hq : q = p+1) (ha : a = q+r) (hm : m = n+1) :
    (Q.pageComplex p n).iCycles ≫ Q.k p q n m hq hm ≫ Q.j q a m ha = 0 := by
  have ha' : a = p+r+1 := by omega
  subst ha'
  subst q m
  simpa only [pageComplex, d] using (Q.pageComplex p n).iCycles_g

/-- k on cycles, with values restricted to the image of i. -/
def cyclesK (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    (Q.pageComplex p n).cycles ⟶ Q.derivedD q m :=
  Q.intoImage q (q+r) m rfl
    ((Q.pageComplex p n).iCycles ≫ Q.k p q n m hq hm)
    (by simpa only [assoc] using Q.cycles_k_j p q (q+r) n m hq rfl hm)

@[reassoc (attr := simp)]
lemma cyclesK_inclusion (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    Q.cyclesK p q n m hq hm ≫ Q.inclusion q m =
      (Q.pageComplex p n).iCycles ≫ Q.k p q n m hq hm := by simp [cyclesK]

lemma toCycles_cyclesK (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    (Q.pageComplex p n).toCycles ≫ Q.cyclesK p q n m hq hm = 0 := by
  rw [← cancel_mono (Q.inclusion q m), assoc, cyclesK_inclusion,
    ← assoc, ShortComplex.toCycles_i]
  dsimp [pageComplex, d]
  rw [assoc, (Q.exact_jk _ _ _ _ _ _ _ _).zero, comp_zero, zero_comp]

/-- k' descends from cycles because k kills boundaries. -/
def derivedK (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    Q.derivedE p n ⟶ Q.derivedD q m :=
  (Q.pageComplex p n).descHomology (Q.cyclesK p q n m hq hm)
    (Q.toCycles_cyclesK p q n m hq hm)

@[reassoc (attr := simp)]
lemma homologyπ_derivedK (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    (Q.pageComplex p n).homologyπ ≫ Q.derivedK p q n m hq hm =
      Q.cyclesK p q n m hq hm := ShortComplex.π_descHomology _ _ _

@[reassoc (attr := simp)]
lemma homologyπ_derivedK_inclusion (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    (Q.pageComplex p n).homologyπ ≫ Q.derivedK p q n m hq hm ≫ Q.inclusion q m =
      (Q.pageComplex p n).iCycles ≫ Q.k p q n m hq hm := by simp

/-- Restriction of i commutes with its image projections. -/
@[reassoc]
lemma projection_derivedI (p n : ℤ) :
    Q.projection (p+1) n ≫ Q.derivedI p (p+1) n rfl =
      Q.i (p+1) (p+1+1) n rfl ≫ Q.projection p n := by
  rw [← cancel_mono (Q.inclusion p n)]
  simp

lemma i_jClass (a b p n : ℤ) (hb : b = a+1) (hp : p = a+r) :
    Q.i a b n hb ≫ Q.jClass a p n hp = 0 := by
  dsimp only [jClass]
  rw [← assoc]
  have h : Q.i a b n hb ≫ Q.jCycles a p n hp = 0 := by
    rw [← cancel_mono (Q.pageComplex p n).iCycles]
    simp only [assoc, jCycles_i, zero_comp]
    exact (Q.exact_ij a b p n hb hp).zero
  rw [h, zero_comp]

lemma derivedI_derivedJ (p q a n : ℤ) (hq : q = p+1) (ha : a = p+(r+1)) :
    Q.derivedI p q n hq ≫ Q.derivedJ p a n ha = 0 := by
  subst q
  rw [← cancel_epi (Q.projection (p+1) n), ← assoc, projection_derivedI,
    assoc, projection_derivedJ, Q.i_jClass (p+1) (p+1+1) a n rfl (by omega), comp_zero]

lemma derivedJ_derivedK (p a b n m : ℤ) (ha : a = p+(r+1))
    (hb : b = a+1) (hm : m = n+1) :
    Q.derivedJ p a n ha ≫ Q.derivedK a b n m hb hm = 0 := by
  rw [← cancel_epi (Q.projection p n), ← assoc, projection_derivedJ]
  rw [← cancel_mono (Q.inclusion b m)]
  simp only [jClass, assoc, homologyπ_derivedK_inclusion, jCycles_i_assoc,
    (Q.exact_jk (p+1) a b n m (by omega) hb hm).zero, comp_zero, zero_comp]

lemma derivedK_derivedI (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    Q.derivedK p q n m hq hm ≫ Q.derivedI p q m hq = 0 := by
  rw [← cancel_epi (Q.pageComplex p n).homologyπ,
    ← cancel_mono (Q.inclusion p m)]
  simp only [assoc, derivedI_inclusion, homologyπ_derivedK_inclusion_assoc,
    (Q.exact_ki p q n m hq hm).zero, comp_zero, zero_comp]

/-- Exactness at the source of i' (the target of k'). -/
lemma derived_exact_ki (p q n m : ℤ) (hq : q = p+1) (hm : m = n+1) :
    ExactPair (Q.derivedK p q n m hq hm) (Q.derivedI p q m hq) := by
  refine ⟨Q.derivedK_derivedI p q n m hq hm, ?_⟩
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  have hx' : (x ≫ Q.inclusion q m) ≫ Q.i p q m hq = 0 := by
    simp only [assoc, ← derivedI_inclusion, reassoc_of% hx, zero_comp]
  obtain ⟨A₁, π, hπ, e, he⟩ :=
    (Q.exact_ki p q n m hq hm).exact.exact_up_to_refinements (x ≫ Q.inclusion q m) hx'
  have hj : Q.inclusion q m ≫ Q.j q (p+r+1) m (by omega) = 0 :=
    image_ι_comp_eq_zero (Q.exact_ij q (q+1) (p+r+1) m rfl (by omega)).zero
  have hecycle : e ≫ (Q.pageComplex p n).g = 0 := by
    have hz : e ≫ Q.k p q n m hq hm ≫ Q.j q (p+r+1) m (by omega) = 0 := by
      rw [← assoc, ← he, assoc, assoc, hj, comp_zero, comp_zero]
    subst q m
    simpa only [pageComplex, d] using hz
  refine ⟨A₁, π, hπ, (Q.pageComplex p n).liftCycles e hecycle ≫
    (Q.pageComplex p n).homologyπ, ?_⟩
  rw [← cancel_mono (Q.inclusion q m)]
  simpa only [assoc, homologyπ_derivedK_inclusion, ShortComplex.liftCycles_i_assoc] using he

/-- Exactness at E'. -/
lemma derived_exact_jk (p a b n m : ℤ) (ha : a = p+(r+1))
    (hb : b = a+1) (hm : m = n+1) :
    ExactPair (Q.derivedJ p a n ha) (Q.derivedK a b n m hb hm) := by
  refine ⟨Q.derivedJ_derivedK p a b n m ha hb hm, ?_⟩
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  obtain ⟨A₁, π₁, hπ₁, e, hecycle, he⟩ :=
    (Q.pageComplex a n).eq_liftCycles_homologyπ_up_to_refinements x
  have hek : e ≫ Q.k a b n m hb hm = 0 := by
    have hz := congrArg (fun f => π₁ ≫ f ≫ Q.inclusion b m) hx
    rw [← assoc, ← assoc, he] at hz
    simpa only [assoc, homologyπ_derivedK_inclusion, ShortComplex.liftCycles_i_assoc,
      zero_comp, comp_zero] using hz
  obtain ⟨A₂, π₂, hπ₂, y, hy⟩ :=
    (Q.exact_jk (p+1) a b n m (by omega) hb hm).exact.exact_up_to_refinements e hek
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y ≫ Q.projection p n, ?_⟩
  simp only [assoc, he, projection_derivedJ, jClass, jCycles,
    ShortComplex.comp_liftCycles_assoc]
  congr 2

/-- Factoring the differential through any correctly indexed D term. -/
lemma d_factor (a b c n m : ℤ) (hb : b = a+1) (hc : c = a+r+1) (hm : m = n+1) :
    Q.d a c n m hc hm = Q.k a b n m hb hm ≫ Q.j b c m (by omega) := by
  subst b
  rfl

lemma k_projection_zero (a p n m : ℤ) (ha : p+1 = a+1) (hm : m = n+1) :
    Q.k a (p+1) n m ha hm ≫ Q.projection p m = 0 := by
  have heq : a = p := by omega
  subst a
  rw [← cancel_mono (Q.inclusion p m)]
  simp only [assoc, projection_inclusion, zero_comp]
  exact (Q.exact_ki p (p+1) n m rfl hm).zero

/-- Exactness at the target of i' (the source of j'). -/
lemma derived_exact_ij (p q a n : ℤ) (hq : q = p+1) (ha : a = p+(r+1)) :
    ExactPair (Q.derivedI p q n hq) (Q.derivedJ p a n ha) := by
  subst q
  refine ⟨Q.derivedI_derivedJ p (p+1) a n rfl ha, ?_⟩
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  obtain ⟨A₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi (Q.projection p n) x
  have hycycle : (y ≫ Q.j (p+1) a n (by omega)) ≫ (Q.pageComplex a n).g = 0 := by
    dsimp only [pageComplex, d]
    rw [assoc, ← assoc (Q.j _ _ _ _), (Q.exact_jk _ _ _ _ _ _ _ _).zero,
      zero_comp, comp_zero]
  have hyclass : (Q.pageComplex a n).liftCycles (y ≫ Q.j (p+1) a n (by omega))
      hycycle ≫ (Q.pageComplex a n).homologyπ = 0 := by
    have hz := congrArg (fun f => π₁ ≫ f) hx
    rw [← assoc, hy, assoc, projection_derivedJ] at hz
    simpa only [jClass, jCycles, ShortComplex.comp_liftCycles_assoc, comp_zero] using hz
  obtain ⟨A₂, π₂, hπ₂, e, he⟩ :=
    ((Q.pageComplex a n).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
      (y ≫ Q.j (p+1) a n (by omega)) hycycle).1 hyclass
  have hboundary : π₂ ≫ y ≫ Q.j (p+1) a n (by omega) =
      e ≫ Q.k (a-r-1) (p+1) (n-1) n (by omega) (by omega) ≫
        Q.j (p+1) a n (by omega) := by
    simpa only [pageComplex, Q.d_factor (a-r-1) (p+1) a (n-1) n (by omega)
      (by omega) (by omega), assoc] using he
  let z := π₂ ≫ y - e ≫ Q.k (a-r-1) (p+1) (n-1) n (by omega) (by omega)
  have hz : z ≫ Q.j (p+1) a n (by omega) = 0 := by
    dsimp only [z]
    rw [Preadditive.sub_comp, assoc, assoc, hboundary, sub_self]
  obtain ⟨A₃, π₃, hπ₃, w, hw⟩ :=
    (Q.exact_ij (p+1) (p+1+1) a n rfl (by omega)).exact.exact_up_to_refinements z hz
  refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, w ≫ Q.projection (p+1) n, ?_⟩
  have hzproj : z ≫ Q.projection p n = π₂ ≫ y ≫ Q.projection p n := by
    dsimp only [z]
    simp only [Preadditive.sub_comp, assoc, Q.k_projection_zero (a-r-1) p (n-1) n (by omega)
      (by omega), comp_zero, sub_zero]
  calc
    (π₃ ≫ π₂ ≫ π₁) ≫ x = π₃ ≫ π₂ ≫ y ≫ Q.projection p n := by simp only [assoc, hy]
    _ = π₃ ≫ z ≫ Q.projection p n := by rw [hzproj]
    _ = w ≫ Q.i (p+1) (p+1+1) n rfl ≫ Q.projection p n := by rw [← assoc, hw, assoc]
    _ = (w ≫ Q.projection (p+1) n) ≫ Q.derivedI p (p+1) n rfl := by
      rw [assoc, projection_derivedI]

/-- The canonical derived exact couple, with the specified representative formulas. -/
def derivation : Q.Derivation where
  i := Q.derivedI
  j := Q.derivedJ
  k := Q.derivedK
  i_formula := Q.derivedI_inclusion
  j_formula := Q.projection_derivedJ
  k_formula := Q.homologyπ_derivedK_inclusion
  exact_ij := Q.derived_exact_ij
  exact_jk := Q.derived_exact_jk
  exact_ki := Q.derived_exact_ki

/-- Repeated derivation, keeping the displacement together with the couple. -/
def iterate : ℕ → Σ s : ℤ, ExactCouple C s
  | 0 => ⟨r, Q⟩
  | t+1 => let prev := iterate t
           ⟨prev.1+1, prev.2.derivation.toExactCouple⟩

lemma iterate_degree (t : ℕ) : (Q.iterate t).1 = r + (t : ℤ) := by
  induction t with
  | zero => simp [iterate]
  | succ t ih => simp [iterate, ih, add_assoc]

end ExactCouple

/-- HA-F05: the homogeneous page differential squares to zero. -/
theorem differential_squared : Specs.AdvancedHomologicalAlgebra.differential_squared_type.{v,u} := by
  intro C _ _ r Q p q a n m l hq ha hm hl
  exact Q.d_squared p q a n m l hq ha hm hl

/-- HA-F05: derivation of any bigraded exact couple in an abelian category. -/
theorem derived_couple_exists (C : Type u) [Category.{v} C] [Abelian C]
    (r : ℤ) (Q : ExactCouple C r) : Nonempty Q.Derivation := ⟨Q.derivation⟩

/-- HA-F05: the derived-couple construction admits every finite iteration. -/
theorem iterate_exact_couples : Specs.AdvancedHomologicalAlgebra.iteration_type.{v,u} := by
  intro C _ _ r Q
  refine ⟨Q.iterate, rfl, ?_, Q.iterate_degree⟩
  intro t
  exact ⟨(Q.iterate t).2.derivation, rfl⟩

end AdvancedHomologicalAlgebra
