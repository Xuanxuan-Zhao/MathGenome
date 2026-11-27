import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.ConeMaps

open CategoryTheory HomologicalComplex

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.HomComplex (HomotopyEquation)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N P : RightDGModule A}

/-- Strict maps agree when their components agree on homogeneous elements. -/
theorem strict_ext {f g : M ⟶ N}
    (h : ∀ a i (x : (M.complex a).X i), (f.app a).f i x = (g.app a).f i x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  exact ModuleCat.hom_ext (LinearMap.ext (h a i))

/-- Right-linear components commuting with consecutive differentials give a strict map. -/
def strictOfComponents
    (F : ∀ a i, (M.complex a).X i →ₗ[k] (N.complex a).X i)
    (dF : ∀ a i (x : (M.complex a).X i),
      (N.complex a).d i (i+1) (F a i x) = F a (i+1) ((M.complex a).d i (i+1) x))
    (aF : ∀ {a b : A.Obj} i j n (h : i+j = n) (x : (M.complex b).X i)
        (z : (A.hom a b).X j),
      F a n (M.act i j n h x z) = N.act i j n h (F b i x) z) :
    M ⟶ N where
  app a := CochainComplex.ofHom (fun i => ModuleCat.ofHom (F a i)) (fun i =>
    ModuleCat.hom_ext (LinearMap.ext (dF a i)))
  comm_act := aF

@[simp] theorem strictOfComponents_apply (F) (dF) (aF) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X i) :
    ((strictOfComponents (M := M) (N := N) F dF aF).app a).f i x = F a i x := rfl

/-- Evaluate the chain map equation of a strict map in consecutive degrees. -/
theorem strict_d (f : M ⟶ N) (a : A.Obj) (i : ℤ) (x : (M.complex a).X i) :
    (N.complex a).d i (i+1) ((f.app a).f i x) =
      (f.app a).f (i+1) ((M.complex a).d i (i+1) x) := by
  exact CategoryTheory.congr_fun ((f.app a).comm i (i+1)) x

/-- The degree `-1` component from degree `i+1` to degree `i`. -/
abbrev hDown (h : GradedHom M N (-1)) (a : A.Obj) (i : ℤ) :
    (M.complex a).X (i+1) ⟶ (N.complex a).X i :=
  h.app a (i+1) i (by omega)

private theorem hDown_act (h : GradedHom M N (-1)) {a b : A.Obj} (i j n : ℤ)
    (e : i+j = n) (x : (M.complex b).X (i+1)) (z : (A.hom a b).X j) :
    hDown h a n (M.act (i+1) j (n+1) (by omega) x z) =
      N.act i j n e (hDown h b i x) z :=
  h.comm_act (i+1) j (n+1) i n (by omega) (by omega) (by omega) x z

private theorem homotopy_index {f g : M ⟶ N} {h : GradedHom M N (-1)}
    (a : A.Obj) (i j : ℤ) (e : i-1 = j) (x : (M.complex a).X i) :
    (f.app a).f i x - (g.app a).f i x =
      (N.complex a).d j i (h.app a i j (by omega) x) +
        h.app a (i+1) i (by omega) ((M.complex a).d i (i+1) x) ↔
      (f.app a).f i x - (g.app a).f i x =
        (N.complex a).d (i-1) i (h.app a i (i-1) (by omega) x) +
          h.app a (i+1) i (by omega) ((M.complex a).d i (i+1) x) := by
  subst j
  rfl

private theorem homotopy_at_succ {f g : M ⟶ N} {h : GradedHom M N (-1)}
    (H : HomotopyEquation f g h) (a : A.Obj) (i : ℤ) (x : (M.complex a).X (i+1)) :
    (f.app a).f (i+1) x - (g.app a).f (i+1) x =
      (N.complex a).d i (i+1) (hDown h a i x) +
        hDown h a (i+1) ((M.complex a).d (i+1) (i+1+1) x) := by
  exact (homotopy_index (f := f) (g := g) (h := h) a (i+1) i (by omega) x).2 (H a (i+1) x)

/-- A component equation on degrees written as successors gives the standard
right-linear homotopy equation in all degrees. -/
theorem homotopyEquationOfSucc {f g : M ⟶ N} {h : GradedHom M N (-1)}
    (H : ∀ a i (x : (M.complex a).X (i+1)),
      (f.app a).f (i+1) x - (g.app a).f (i+1) x =
        (N.complex a).d i (i+1) (hDown h a i x) +
          hDown h a (i+1) ((M.complex a).d (i+1) (i+1+1) x)) :
    HomotopyEquation f g h := by
  intro a i x
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, j+1 = i := ⟨i-1, by omega⟩
  exact (homotopy_index (f := f) (g := g) (h := h) a (j+1) j (by omega) x).1 (H a j x)

section ConeMap

variable {M' N' : RightDGModule A}
variable (f : M ⟶ N) (g : M' ⟶ N') (a₀ : M ⟶ M') (b₀ : N ⟶ N')
variable (h : GradedHom M N' (-1))

private def coneMapComponents (a : A.Obj) (i : ℤ) :
    ((cone f).complex a).X i →ₗ[k] ((cone g).complex a).X i :=
  ((((b₀.app a).f i).hom.comp (LinearMap.fst _ _ _)) +
    ((hDown h a i).hom.comp (LinearMap.snd _ _ _))).prod
      (((a₀.app a).f (i+1)).hom.comp (LinearMap.snd _ _ _))

private theorem coneMapComponents_apply (a : A.Obj) (i : ℤ) (p : ((cone f).complex a).X i) :
    coneMapComponents f g a₀ b₀ h a i p =
      ((b₀.app a).f i p.1 + hDown h a i p.2, (a₀.app a).f (i+1) p.2) := rfl

/-- The cone map associated to a right-linear homotopy of a square. -/
def coneMapOfHomotopy (H : HomotopyEquation (f ≫ b₀) (a₀ ≫ g) h) : cone f ⟶ cone g :=
  strictOfComponents (coneMapComponents f g a₀ b₀ h) (by
    intro a i p
    rw [coneMapComponents_apply, cone_d, cone_d, coneMapComponents_apply]
    have e := homotopy_at_succ H a i p.2
    simp only [RightDGModuleModel.comp_app, HomologicalComplex.comp_f, ModuleCat.comp_apply] at e
    apply Prod.ext
    · dsimp only
      rw [map_add, strict_d, map_add, map_neg]
      rw [sub_eq_iff_eq_add.mp e]
      abel
    · dsimp only
      rw [strict_d, map_neg]) (by
    intro a b i j n e p z
    rw [coneMapComponents_apply, cone_act, cone_act, coneMapComponents_apply]
    apply Prod.ext
    · dsimp only
      rw [b₀.comm_act, hDown_act h i j n e, map_add, LinearMap.add_apply]
    · exact a₀.comm_act (i+1) j (n+1) (by omega) p.2 z)

@[simp] theorem coneMapOfHomotopy_apply (H : HomotopyEquation (f ≫ b₀) (a₀ ≫ g) h)
    (a : A.Obj) (i : ℤ) (p : ((cone f).complex a).X i) :
    ((coneMapOfHomotopy f g a₀ b₀ h H).app a).f i p =
      ((b₀.app a).f i p.1 + hDown h a i p.2, (a₀.app a).f (i+1) p.2) := rfl

/-- The chosen comparison intertwines target inclusions. -/
theorem coneMap_in (H : HomotopyEquation (f ≫ b₀) (a₀ ≫ g) h) :
    coneInclusion f ≫ coneMapOfHomotopy f g a₀ b₀ h H = b₀ ≫ coneInclusion g := by
  apply strict_ext
  intro a i y
  change ((coneMapOfHomotopy f g a₀ b₀ h H).app a).f i (y, 0) =
    ((b₀.app a).f i y, 0)
  rw [coneMapOfHomotopy_apply, map_zero, map_zero, add_zero]

/-- The chosen comparison intertwines the positive quotient projections. -/
theorem coneMap_out (H : HomotopyEquation (f ≫ b₀) (a₀ ≫ g) h) :
    coneMapOfHomotopy f g a₀ b₀ h H ≫ coneProjection g = coneProjection f ≫ shiftMap 1 a₀ := by
  apply strict_ext
  intro a i p
  rfl

end ConeMap

/-- The strict comparison with its two commuting squares and component formula. -/
theorem exists_coneMapOfHomotopy :
    Specs.DerivedFormalization.DG.ConeMaps.ConeSquareComparison.{u,v,w} := by
  intro k _ A M N M' N' f g a b h H
  exact ⟨coneMapOfHomotopy f g a b h H, coneMap_in f g a b h H,
    coneMap_out f g a b h H, coneMapOfHomotopy_apply f g a b h H⟩

/-- A right-linear family on degrees `i+1 → i` defines a homogeneous map of degree `-1`. -/
def homotopyOfComponents
    (F : ∀ a i, (M.complex a).X (i+1) →ₗ[k] (N.complex a).X i)
    (aF : ∀ {a b : A.Obj} i j n (e : i+j = n) (x : (M.complex b).X (i+1))
        (z : (A.hom a b).X j),
      F a n (M.act (i+1) j (n+1) (by omega) x z) =
        N.act i j n e (F b i x) z) :
    GradedHom M N (-1) :=
  GradedHom.mk (fun a i q e => by
    have h : q+1 = i := by omega
    subst i
    exact ModuleCat.ofHom (F a q)) (by
    intro a b i j n ir nr e ei en x z
    have hi : ir+1 = i := by omega
    have hn : nr+1 = n := by omega
    subst i n
    exact aF ir j nr (by omega) x z)

@[simp] theorem homotopyOfComponents_apply (F) (aF) (a : A.Obj) (i : ℤ)
    (x : (M.complex a).X (i+1)) :
    hDown (homotopyOfComponents (M := M) (N := N) F aF) a i x = F a i x := rfl

private def strictConeMap {M' N' : RightDGModule A}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N') (e : f ≫ b = a ≫ g) :
    cone f ⟶ cone g :=
  coneMapOfHomotopy f g a b 0 (by
    rw [e]
    intro o i x
    change (g.app o).f i ((a.app o).f i x) - (g.app o).f i ((a.app o).f i x) =
      (N'.complex o).d (i-1) i (0 : (N'.complex o).X (i-1)) + 0
    simp)

private theorem strictConeMap_apply {M' N' : RightDGModule A}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N') (e : f ≫ b = a ≫ g)
    (o : A.Obj) (i : ℤ) (p : ((cone f).complex o).X i) :
    ((strictConeMap f g a b e).app o).f i p =
      ((b.app o).f i p.1, (a.app o).f (i+1) p.2) := by
  change ((b.app o).f i p.1 + 0, (a.app o).f (i+1) p.2) = _
  rw [add_zero]

section Octahedron

variable (f : M ⟶ N) (g : N ⟶ P)

/-- The cone comparison for the square with vertical arrows `𝟙 M` and `g`. -/
def firstConeMap : cone f ⟶ cone (f ≫ g) :=
  strictConeMap f (f ≫ g) (𝟙 M) g (by rw [Category.id_comp])

/-- The cone comparison for the square with vertical arrows `f` and `𝟙 P`. -/
def secondConeMap : cone (f ≫ g) ⟶ cone g :=
  strictConeMap (f ≫ g) g f (𝟙 P) (by rw [Category.comp_id])

@[simp] theorem firstConeMap_apply (o : A.Obj) (i : ℤ)
    (p : ((cone f).complex o).X i) :
    ((firstConeMap f g).app o).f i p = ((g.app o).f i p.1, p.2) :=
  strictConeMap_apply _ _ _ _ _ _ _ _

@[simp] theorem secondConeMap_apply (o : A.Obj) (i : ℤ)
    (p : ((cone (f ≫ g)).complex o).X i) :
    ((secondConeMap f g).app o).f i p = (p.1, (f.app o).f (i+1) p.2) :=
  strictConeMap_apply _ _ _ _ _ _ _ _

theorem firstConeMap_inclusion :
    coneInclusion f ≫ firstConeMap f g = g ≫ coneInclusion (f ≫ g) := by
  apply strict_ext
  intro a i y
  exact firstConeMap_apply f g a i (y, 0)

theorem firstConeMap_projection :
    firstConeMap f g ≫ coneProjection (f ≫ g) = coneProjection f := by
  apply strict_ext
  intro a i p
  exact congrArg Prod.snd (firstConeMap_apply f g a i p)

theorem secondConeMap_inclusion :
    coneInclusion (f ≫ g) ≫ secondConeMap f g = coneInclusion g := by
  apply strict_ext
  intro a i z
  change ((secondConeMap f g).app a).f i (z, 0) = (z, 0)
  rw [secondConeMap_apply, map_zero]

theorem secondConeMap_projection :
    secondConeMap f g ≫ coneProjection g = coneProjection (f ≫ g) ≫ shiftMap 1 f := by
  apply strict_ext
  intro a i p
  exact congrArg Prod.snd (secondConeMap_apply f g a i p)

private theorem octahedronCone_d (a : A.Obj) (i : ℤ)
    (p : ((cone (firstConeMap f g)).complex a).X i) :
    ((cone (firstConeMap f g)).complex a).d i (i+1) p =
      (((P.complex a).d i (i+1) p.1.1 + (g.app a).f (i+1) ((f.app a).f (i+1) p.1.2) +
          (g.app a).f (i+1) p.2.1, -(M.complex a).d (i+1) (i+1+1) p.1.2 + p.2.2),
        (-((N.complex a).d (i+1) (i+1+1) p.2.1 + (f.app a).f (i+1+1) p.2.2),
          (M.complex a).d (i+1+1) (i+1+1+1) p.2.2)) := by
  rw [cone_d (firstConeMap f g), cone_d (f ≫ g), firstConeMap_apply, cone_d f]
  exact Prod.ext rfl (Prod.ext rfl (neg_neg _))

/-- The strict retraction from the cone of the first comparison onto the cone of `g`. -/
def octahedronReadout : cone (firstConeMap f g) ⟶ cone g :=
  strictOfComponents (M := cone (firstConeMap f g)) (N := cone g)
    (fun a i => (LinearMap.fst _ _ _ ∘ₗ LinearMap.fst _ _ _).prod
      ((((f.app a).f (i+1)).hom ∘ₗ LinearMap.snd _ _ _ ∘ₗ LinearMap.fst _ _ _) +
        (LinearMap.fst _ _ _ ∘ₗ LinearMap.snd _ _ _)))
    (by
      intro a i p
      let d := ((cone (firstConeMap f g)).complex a).d i (i+1) p
      change ((cone g).complex a).d i (i+1) (p.1.1, (f.app a).f (i+1) p.1.2 + p.2.1) =
        (d.1.1, (f.app a).f (i+1+1) d.1.2 + d.2.1)
      dsimp only [d]
      rw [octahedronCone_d f g, cone_d g]
      apply Prod.ext
      · dsimp only
        rw [map_add]
        abel
      · dsimp only
        rw [map_add, map_add, map_neg, strict_d]
        abel)
    (by
      intro a b i j n e p z
      apply Prod.ext
      · rfl
      · change (f.app a).f (n+1) (M.act (i+1) j (n+1) (by omega) p.1.2 z) +
          N.act (i+1) j (n+1) (by omega) p.2.1 z =
          N.act (i+1) j (n+1) (by omega) ((f.app b).f (i+1) p.1.2 + p.2.1) z
        rw [f.comm_act, map_add, LinearMap.add_apply])

/-- The strict section of the retraction. -/
def octahedronSection : cone g ⟶ cone (firstConeMap f g) :=
  strictOfComponents (M := cone g) (N := cone (firstConeMap f g))
    (fun _ _ => ((LinearMap.fst _ _ _).prod 0).prod ((LinearMap.snd _ _ _).prod 0))
    (by
      intro a i p
      let d := ((cone g).complex a).d i (i+1) p
      change ((cone (firstConeMap f g)).complex a).d i (i+1) ((p.1,0),(p.2,0)) =
        ((d.1,0),(d.2,0))
      dsimp only [d]
      rw [octahedronCone_d f g, cone_d g]
      dsimp only
      simp only [map_zero, neg_zero, add_zero])
    (by
      intro a b i j n e p z
      change ((P.act i j n e p.1 z,0),
        (N.act (i+1) j (n+1) (by omega) p.2 z,0)) =
        ((P.act i j n e p.1 z, M.act (i+1) j (n+1) (by omega) 0 z),
          (N.act (i+1) j (n+1) (by omega) p.2 z, M.act (i+1+1) j (n+1+1) (by omega) 0 z))
      simp only [map_zero, LinearMap.zero_apply])

/-- The right-linear homotopy from retraction followed by section to the identity. -/
def octahedronHomotopy :
    GradedHom (cone (firstConeMap f g)) (cone (firstConeMap f g)) (-1) :=
  homotopyOfComponents
    (fun _ _ => (0 : _ →ₗ[k] _).prod ((0 : _ →ₗ[k] _).prod
      (-(LinearMap.snd _ _ _ ∘ₗ LinearMap.fst _ _ _))))
    (by
      intro a b i j n e p z
      change ((0,0),(0,-(M.act (i+1+1) j (n+1+1) (by omega) p.1.2 z))) =
        ((P.act i j n e 0 z, M.act (i+1) j (n+1) (by omega) 0 z),
          (N.act (i+1) j (n+1) (by omega) 0 z, M.act (i+1+1) j (n+1+1) (by omega) (-p.1.2) z))
      simp only [map_zero, map_neg, LinearMap.zero_apply, LinearMap.neg_apply])

@[simp] theorem octahedronReadout_apply (a : A.Obj) (i : ℤ)
    (p : ((cone (firstConeMap f g)).complex a).X i) :
    ((octahedronReadout f g).app a).f i p =
      (p.1.1, (f.app a).f (i+1) p.1.2 + p.2.1) := rfl

@[simp] theorem octahedronSection_apply (a : A.Obj) (i : ℤ)
    (p : ((cone g).complex a).X i) :
    ((octahedronSection f g).app a).f i p = ((p.1, 0), (p.2, 0)) := rfl

@[simp] theorem octahedronHomotopy_apply (a : A.Obj) (i : ℤ)
    (p : ((cone (firstConeMap f g)).complex a).X (i+1)) :
    hDown (octahedronHomotopy f g) a i p = ((0, 0), (0, -p.1.2)) := rfl

theorem octahedron_id_left :
    octahedronSection f g ≫ octahedronReadout f g = 𝟙 (cone g) := by
  apply strict_ext
  intro a i p
  change (p.1, (f.app a).f (i+1) 0 + p.2) = p
  simp

theorem octahedron_homotopy :
    HomotopyEquation (octahedronReadout f g ≫ octahedronSection f g)
      (𝟙 (cone (firstConeMap f g))) (octahedronHomotopy f g) := by
  apply homotopyEquationOfSucc
  intro a i p
  change (((p.1.1,0),((f.app a).f (i+1+1) p.1.2 + p.2.1,0)) - p) =
    ((cone (firstConeMap f g)).complex a).d i (i+1) ((0,0),(0,-p.1.2)) +
      ((0,0),(0,-(((cone (firstConeMap f g)).complex a).d (i+1) (i+1+1) p).1.2))
  rw [octahedronCone_d f g a i, octahedronCone_d f g a (i+1)]
  simp only [Prod.add_def, Prod.sub_def, map_zero, map_neg, add_zero,
    zero_add, neg_zero, neg_neg, zero_sub, sub_self]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> abel



theorem octahedron_inclusion :
    coneInclusion (firstConeMap f g) ≫ octahedronReadout f g = secondConeMap f g := by
  apply strict_ext
  intro a i p
  change (p.1, (f.app a).f (i+1) p.2 + 0) = ((secondConeMap f g).app a).f i p
  rw [add_zero, secondConeMap_apply]

theorem octahedron_projection :
    octahedronSection f g ≫ coneProjection (firstConeMap f g) =
      coneProjection g ≫ shiftMap 1 (coneInclusion f) := by
  apply strict_ext
  intro a i p
  rfl

end Octahedron

/-- The strict octahedral maps and the right-linear homotopy for the iterated cone. -/
theorem octahedronConeComparison :
    Specs.DerivedFormalization.DG.ConeMaps.OctahedronConeComparison.{u,v,w} := by
  intro k _ A M N P f g
  exact ⟨firstConeMap f g, secondConeMap f g, octahedronReadout f g,
    octahedronSection f g, octahedronHomotopy f g, firstConeMap_apply f g,
    secondConeMap_apply f g, firstConeMap_inclusion f g, firstConeMap_projection f g,
    secondConeMap_inclusion f g, secondConeMap_projection f g, octahedronReadout_apply f g,
    octahedronSection_apply f g, octahedronHomotopy_apply f g, octahedron_id_left f g,
    octahedron_homotopy f g, octahedron_inclusion f g, octahedron_projection f g⟩

end DerivedFormalization.RightDGModule
