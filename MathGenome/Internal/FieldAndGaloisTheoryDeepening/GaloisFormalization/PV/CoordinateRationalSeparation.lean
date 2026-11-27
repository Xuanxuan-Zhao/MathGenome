import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LineStabilizerRepresentation
import Batteries.Tactic.OpenPrivate
import Mathlib.GroupTheory.CosetCover
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.CoordinateRationalSeparation

namespace GaloisFormalization.PV.CoordinateRationalSeparation

open MatrixGroupCoordinates
open GaloisFormalization.PV.CoordinateRationalSeparation.Specs (GroupCoordinateRing TotalCoordinateRing extendToTotal)
open scoped MatrixGroupCoordinates.Specs

universe u

noncomputable section

section Translation

variable {C : Type u} [Field C] {n : ℕ} (G : Subgroup (GL (Fin n) C))

open private regular_iff_mem_range evaluateSecond_product evaluateSecond_mem_range
  productPolynomial from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.LineStabilizerRepresentation

private theorem exists_translate (g : G) (r : GroupCoordinateRing G) :
    ∃ s : GroupCoordinateRing G, ∀ x : G, evalCoordinate x s = evalCoordinate (x * g) r := by
  let S : Set (GL (Fin n) C) := G
  apply (regular_iff_coordinate S _).mp
  obtain ⟨p, rfl⟩ := coordinateMap_surjective S r
  apply (regular_iff_mem_range G _).mpr
  convert evaluateSecond_mem_range G (productPolynomial p) g using 1
  funext x
  exact (evaluateSecond_product G x g p).symm

private def translateHom (g : G) : GroupCoordinateRing G →ₐ[C] GroupCoordinateRing G where
  toFun r := (exists_translate G g r).choose
  map_zero' := coordinate_ext _ _ _ fun x => by
    rw [(exists_translate G g 0).choose_spec x, map_zero, map_zero]
  map_one' := coordinate_ext _ _ _ fun x => by
    rw [(exists_translate G g 1).choose_spec x, map_one, map_one]
  map_add' r s := coordinate_ext _ _ _ fun x => by
    rw [(exists_translate G g (r + s)).choose_spec x, map_add, map_add,
      (exists_translate G g r).choose_spec x, (exists_translate G g s).choose_spec x]
  map_mul' r s := coordinate_ext _ _ _ fun x => by
    rw [(exists_translate G g (r * s)).choose_spec x, map_mul, map_mul,
      (exists_translate G g r).choose_spec x, (exists_translate G g s).choose_spec x]
  commutes' c := coordinate_ext _ _ _ fun x => by
    rw [(exists_translate G g _).choose_spec x, AlgHom.commutes, AlgHom.commutes]

private theorem eval_translateHom (g x : G) (r : GroupCoordinateRing G) :
    evalCoordinate x (translateHom G g r) = evalCoordinate (x * g) r :=
  (exists_translate G g r).choose_spec x

private theorem translateHom_inverse (g : G) :
    (translateHom G g).comp (translateHom G g⁻¹) = AlgHom.id C (GroupCoordinateRing G) := by
  ext r
  apply coordinate_ext
  intro x
  change evalCoordinate x (translateHom G g (translateHom G g⁻¹ r)) = evalCoordinate x r
  rw [eval_translateHom, eval_translateHom, mul_inv_cancel_right]

private def translateEquiv (g : G) : GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G :=
  AlgEquiv.ofAlgHom (translateHom G g) (translateHom G g⁻¹) (translateHom_inverse G g)
    (by simpa only [inv_inv] using translateHom_inverse G g⁻¹)

private theorem eval_translateEquiv (g x : G) (r : GroupCoordinateRing G) :
    evalCoordinate x (translateEquiv G g r) = evalCoordinate (x * g) r :=
  eval_translateHom G g x r

/-- Pullback by right translation is a left action on coordinate functions. -/
theorem exists_rightTranslation : Specs.ExistsRightTranslation.{u} := by
  intro C _ n G
  let τ : G →* (GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G) :=
    { toFun := translateEquiv G
      map_one' := by
        apply AlgEquiv.ext
        intro r
        apply coordinate_ext
        intro x
        change evalCoordinate x (translateEquiv G 1 r) = evalCoordinate x r
        rw [eval_translateEquiv, mul_one]
      map_mul' g h := by
        apply AlgEquiv.ext
        intro r
        apply coordinate_ext
        intro x
        change evalCoordinate x (translateEquiv G (g * h) r) =
          evalCoordinate x (translateEquiv G g (translateEquiv G h r))
        rw [eval_translateEquiv, eval_translateEquiv, eval_translateEquiv, mul_assoc] }
  exact ⟨τ, eval_translateEquiv G⟩

end Translation

private theorem isClosed_coordinateZeros {C : Type u} [Field C] {n : ℕ}
    (G : Subgroup (GL (Fin n) C)) (r : GroupCoordinateRing G) :
    IsClosed {x : G | evalCoordinate x r = 0} := by
  let S : Set (GL (Fin n) C) := G
  obtain ⟨p, rfl⟩ := coordinateMap_surjective S r
  apply (isClosed_subtype_iff_zeroLocus S _).mpr
  refine ⟨{p}, ?_⟩
  ext x
  change evalCoordinate (S := S) x (coordinateMap S p) = 0 ↔
    ∀ q ∈ ({p} : Set (CoordinatePolynomial C n)), evalAt (C := C) x.val q = 0
  rw [evalCoordinate_mk]
  simp

theorem nonZeroDivisor_of_components : Specs.NonZeroDivisorOfComponents.{u} := by
  intro C _ n G r hr
  apply mem_nonZeroDivisors_iff_left.mpr
  intro s hrs
  apply coordinate_ext (G : Set (GL (Fin n) C)) s 0
  intro x
  rw [map_zero]
  by_contra hx
  let X := irreducibleComponent x
  obtain ⟨y, hyX, hya⟩ := hr X (irreducibleComponent_mem_irreducibleComponents x)
  have hU : IsOpen ({y : G | evalCoordinate y r = 0}ᶜ) :=
    (isClosed_coordinateZeros G r).isOpen_compl
  have hV : IsOpen ({y : G | evalCoordinate y s = 0}ᶜ) :=
    (isClosed_coordinateZeros G s).isOpen_compl
  obtain ⟨z, _, hzr, hzs⟩ :=
    (irreducibleComponent_mem_irreducibleComponents x).1.2 _ _ hU hV
      ⟨y, hyX, hya⟩ ⟨x, mem_irreducibleComponent, hx⟩
  have hz : evalCoordinate z r * evalCoordinate z s = 0 := by
    rw [← map_mul, hrs, map_zero]
  exact (mul_ne_zero hzr hzs) hz

section Separator

variable {C : Type u} [Field C] {n : ℕ} (G : Subgroup (GL (Fin n) C)) {m : ℕ}

private theorem exists_form_nonzero [Infinite C] {ι : Type*} [Finite ι]
    (v : ι → Fin m → C) (hv : ∀ i, v i ≠ 0) :
    ∃ a : (Fin m → C) →ₗ[C] C, ∀ i, a (v i) ≠ 0 := by
  let kernels (i : ι) :=
    LinearMap.ker (LinearMap.applyₗ (R := C) (M₂ := C) (v i))
  by_contra! h
  have hcover : ⋃ i, (kernels i : Set ((Fin m → C) →ₗ[C] C)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨i, hi⟩ := h a
    exact Set.mem_iUnion.mpr ⟨i, LinearMap.mem_ker.mpr hi⟩
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
  apply hv i
  funext j
  have hproj : (LinearMap.proj j : (Fin m → C) →ₗ[C] C) ∈ kernels i := by
    rw [hi]
    exact Submodule.mem_top
  exact LinearMap.mem_ker.mp hproj

private theorem exists_form_on_components [Infinite C] (g : G)
    (v : G → Fin m → C) (hv : ∀ x, v x ≠ 0) :
    ∃ a : (Fin m → C) →ₗ[C] C,
      a (v 1) ≠ 0 ∧ a (v g) ≠ 0 ∧
        ∀ X ∈ irreducibleComponents G, ∃ x ∈ X, a (v x) ≠ 0 := by
  let : TopologicalSpace.NoetherianSpace (GL (Fin n) C) := zariski_noetherian
  let : TopologicalSpace.NoetherianSpace G :=
    TopologicalSpace.NoetherianSpace.set (G : Set (GL (Fin n) C))
  have : Finite (irreducibleComponents G) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := G)).to_subtype
  let point (X : irreducibleComponents G) : G := X.2.1.1.choose
  let S : Set G := insert 1 (insert g (Set.range point))
  have : Finite S := ((Set.finite_range point).insert g |>.insert 1).to_subtype
  obtain ⟨a, ha⟩ := exists_form_nonzero (fun x : S => v x.val) (fun x => hv x.val)
  refine ⟨a, ha ⟨1, Set.mem_insert _ _⟩,
    ha ⟨g, Set.mem_insert_of_mem _ (Set.mem_insert _ _)⟩, ?_⟩
  intro X hX
  let Y : irreducibleComponents G := ⟨X, hX⟩
  exact ⟨point Y, Y.2.1.1.choose_spec,
    ha ⟨point Y, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_range_self Y))⟩⟩

private theorem exists_orbit_coordinate (ρ : G →* GL (Fin m) C)
    (hρ : IsRegularRepresentation ρ) (w : Fin m → C) (l : (Fin m → C) →ₗ[C] C) :
    ∃ r : GroupCoordinateRing G, ∀ x : G, evalCoordinate x r = l (Matrix.toLin' (ρ x).val w) := by
  classical
  let S : Set (GL (Fin n) C) := G
  choose p hp using fun i j => (regular_iff_coordinate S _).mp (hρ.1 i j)
  let q (i : Fin m) : GroupCoordinateRing G := ∑ j, p i j * algebraMap C _ (w j)
  have hq (i : Fin m) (x : G) :
      evalCoordinate x (q i) = Matrix.toLin' (ρ x).val w i := by
    simp only [q, map_sum, map_mul, hp, AlgHom.commutes, Algebra.algebraMap_self_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  let B := Pi.basisFun C (Fin m)
  refine ⟨∑ i, q i * algebraMap C _ (l (B i)), fun x => ?_⟩
  have expansion (z : Fin m → C) : ∑ i, z i • B i = z := by
    simpa only [B, Pi.basisFun_repr] using B.sum_repr z
  have h := congrArg l (expansion (Matrix.toLin' (ρ x).val w))
  simpa only [map_sum, map_mul, hq, AlgHom.commutes, Algebra.algebraMap_self_apply,
    LinearMap.map_smul, smul_eq_mul] using h

private theorem extend_fraction_eq_iff
    (e : GroupCoordinateRing G ≃ₐ[C] GroupCoordinateRing G)
    (r : GroupCoordinateRing G) (d : nonZeroDivisors (GroupCoordinateRing G)) :
    extendToTotal e (IsLocalization.mk' (TotalCoordinateRing G) r d) =
      IsLocalization.mk' (TotalCoordinateRing G) r d ↔ e r * d.val = r * e d.val := by
  let A := GroupCoordinateRing G
  let Q := TotalCoordinateRing G
  have hM : (nonZeroDivisors A).map e.toRingEquiv.toMonoidHom = nonZeroDivisors A :=
    MulEquivClass.map_nonZeroDivisors e.toRingEquiv
  change IsLocalization.ringEquivOfRingEquiv Q Q e.toRingEquiv hM
    (IsLocalization.mk' Q r d) = IsLocalization.mk' Q r d ↔ e r * d.val = r * e d.val
  rw [IsLocalization.ringEquivOfRingEquiv_mk', IsLocalization.mk'_eq_iff_eq',
    (IsFractionRing.injective A Q).eq_iff]
  rfl

/-- The ratio of two linear forms on a regular orbit separates the specified coset. -/
theorem exists_coordinateRationalSeparator : Specs.ExistsCoordinateRationalSeparator.{u} := by
  classical
  intro C _ _ _ n G hG H hH g hg τ hτ
  obtain ⟨m, ρ, w, hρ, hw, hstab⟩ :=
    LineStabilizerRepresentation.exists_lineStabilizerRepresentation G hG H hH
  let v (x : G) := Matrix.toLin' (ρ x).val w
  have v_one : v 1 = w := by
    simp [v]
  have v_mul (x y : G) : v (x * y) = Matrix.toLin' (ρ x).val (v y) := by
    simp only [v, map_mul, Units.val_mul, Matrix.toLin'_mul_apply]
  have hv (x : G) : v x ≠ 0 := by
    intro hx
    apply hw
    calc
      w = v (x⁻¹ * x) := by rw [inv_mul_cancel, v_one]
      _ = 0 := by rw [v_mul, hx, map_zero]
  obtain ⟨a, ha₁, hag, haX⟩ := exists_form_on_components G g v hv
  have hnorm : (a (v 1))⁻¹ • v 1 ≠ (a (v g))⁻¹ • v g := by
    intro h
    have hspan (x : G) (hx : a (v x) ≠ 0) :
        Submodule.span C {(a (v x))⁻¹ • v x} = Submodule.span C {v x} :=
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hx)) _
    have heq : Submodule.span C {v 1} = Submodule.span C {v g} := by
      rw [← hspan 1 ha₁, ← hspan g hag, h]
    apply hg
    apply (hstab g).mp
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span C {v g} = Submodule.span C {w}
    exact heq.symm.trans (congrArg (fun z => Submodule.span C {z}) v_one)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hnorm
  let b : (Fin m → C) →ₗ[C] C := LinearMap.proj i
  have hratiov : b (v 1) / a (v 1) ≠ b (v g) / a (v g) := by
    simpa only [b, LinearMap.proj_apply, div_eq_mul_inv, mul_comm, Pi.smul_apply,
      smul_eq_mul] using hi
  obtain ⟨s, hs⟩ := exists_orbit_coordinate G ρ hρ w a
  obtain ⟨r, hr⟩ := exists_orbit_coordinate G ρ hρ w b
  have hsX : ∀ X ∈ irreducibleComponents G, ∃ x ∈ X, evalCoordinate x s ≠ 0 := by
    simpa only [hs] using haX
  let d : nonZeroDivisors (GroupCoordinateRing G) := ⟨s, nonZeroDivisor_of_components G s hsX⟩
  have hs₁ : evalCoordinate (1 : G) s ≠ 0 := by simpa only [hs] using ha₁
  have hsg : evalCoordinate g s ≠ 0 := by simpa only [hs] using hag
  have hratio : evalCoordinate (1 : G) r / evalCoordinate (1 : G) s ≠
      evalCoordinate g r / evalCoordinate g s := by
    simpa only [hr, hs] using hratiov
  have hfixed (h : H) : τ h.val r * s = r * τ h.val s := by
    have hmem : v h.val ∈ Submodule.span C {w} := by
      rw [← (hstab h.val).mpr h.prop]
      exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hscale (x : G) : v (x * h.val) = c • v x := by
      rw [v_mul, ← hc, LinearMap.map_smul]
    apply coordinate_ext
    intro x
    rw [map_mul, map_mul, hτ h.val x r, hτ h.val x s, hr, hs, hr, hs]
    change b (v (x * h.val)) * a (v x) = b (v x) * a (v (x * h.val))
    simp only [hscale, LinearMap.map_smul, smul_eq_mul]
    ac_rfl
  refine ⟨m, ρ, w, a, b, d, r, hρ, hw, hstab, hs, hr, hsX, hs₁, hsg, hratio, hfixed,
    fun h => (extend_fraction_eq_iff G (τ h.val) r d).mpr (hfixed h), ?_⟩
  intro he
  have heq := (extend_fraction_eq_iff G (τ g) r d).mp he
  apply hratio
  apply (div_eq_div_iff hs₁ hsg).mpr
  have heval := congrArg (evalCoordinate (1 : G)) heq
  rw [map_mul, map_mul, hτ g 1 r, hτ g 1 d.val, one_mul] at heval
  exact heval.symm

end Separator

end

end GaloisFormalization.PV.CoordinateRationalSeparation
