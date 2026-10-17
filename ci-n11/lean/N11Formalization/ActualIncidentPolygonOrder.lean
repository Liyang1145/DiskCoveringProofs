import N11Formalization.ActualVoronoiLocalFan

/-! An ACTUAL incident circle has a bijective strict angular order, including
the4/5-site cocircular cases. This order is about the actual primal vertex,
not about the origin and not the canonical source face table. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualIncidentPolygonOrder
open ActualVoronoiCells ActualVoronoiIncidence ActualDelaunaySupport
open ActualVoronoiLocalFan

def siteAngle (c : Fin 11 → Point) (v : Point) (i : Fin 11) : ℝ :=
  circleAngle (centerDir (c i-v))

theorem InteriorFace.site_ne_vertex {c : Fin 11 → Point} {r : ℝ}
    (f : InteriorFace c r) (hc : Function.Injective c)
    {i : Fin 11} (hi : i ∈ incident c f.point) : c i-f.point ≠ 0 := by
  obtain ⟨j,hj,hji⟩ := Finset.exists_mem_ne (s := incident c f.point) (by
    have h := f.at_least_three
    omega) i
  have hp := common_nearest_radius_pos hc hji.symm
    (mem_incident.mp hi) (mem_incident.mp hj)
  intro he
  have hi0 : c i = f.point := sub_eq_zero.mp he
  rw [hi0,dist_self] at hp
  exact (lt_irrefl 0) hp

theorem InteriorFace.siteAngle_injective {c : Fin 11 → Point} {r : ℝ}
    (f : InteriorFace c r) (hc : Function.Injective c) :
    Function.Injective (fun i : {i : Fin 11 // i ∈ incident c f.point} =>
      siteAngle c f.point i.val) := by
  intro i j he
  have hi := InteriorFace.site_ne_vertex f hc i.property
  have hj := InteriorFace.site_ne_vertex f hc j.property
  have hd : centerDir (c i.val-f.point) = centerDir (c j.val-f.point) := by
    calc
      _ = circleMap (siteAngle c f.point i.val) :=
        (circleMap_circleAngle _ (centerDir_norm hi)).symm
      _ = circleMap (siteAngle c f.point j.val) := congrArg circleMap he
      _ = _ := circleMap_circleAngle _ (centerDir_norm hj)
  have hn : ‖c i.val-f.point‖ = ‖c j.val-f.point‖ := by
    simpa only [← dist_eq_norm,dist_comm] using
      f.equal_radius i.val i.property j.val j.property
  have hs : c i.val-f.point = c j.val-f.point := by
    calc
      _ = ‖c i.val-f.point‖ • centerDir (c i.val-f.point) :=
        self_eq_norm_smul_centerDir hi
      _ = ‖c j.val-f.point‖ • centerDir (c j.val-f.point) := by rw [hd,hn]
      _ = _ := (self_eq_norm_smul_centerDir hj).symm
  exact Subtype.ext (hc (sub_left_inj.mp hs))

structure OrderedCircle (c : Fin 11 → Point) (r : ℝ) (f : InteriorFace c r) where
  order : Fin (incident c f.point).card ≃ {i : Fin 11 // i ∈ incident c f.point}
  sorted : StrictMono (fun j => siteAngle c f.point (order j).val)
  radius : ℝ
  positive : 0 < radius
  radius_le : radius ≤ r
  coordinates : ∀ j, c (order j).val =
    f.point+radius • circleMap (siteAngle c f.point (order j).val)

theorem InteriorFace.orderedCircle {c : Fin 11 → Point} {r : ℝ}
    (f : InteriorFace c r) (hc : Function.Injective c) :
    Nonempty (OrderedCircle c r f) := by
  classical
  let I := {i : Fin 11 // i ∈ incident c f.point}
  let a : I → ℝ := fun i => siteAngle c f.point i.val
  have ha : Function.Injective a := InteriorFace.siteAngle_injective f hc
  let S : Finset ℝ := (incident c f.point).image (siteAngle c f.point)
  have hcard : S.card = (incident c f.point).card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact congrArg Subtype.val (ha (show a ⟨i,hi⟩ = a ⟨j,hj⟩ from he))
  let g : I → S := fun i => ⟨a i,Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j he
      exact ha (congrArg Subtype.val he)
    · intro y
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨i,hi⟩,Subtype.ext he⟩
  let q : I ≃ S := Equiv.ofBijective g hg
  let e : Fin (incident c f.point).card ≃o S := S.orderIsoOfFin hcard
  let p : Fin (incident c f.point).card ≃ I := e.toEquiv.trans q.symm
  have he (j : Fin (incident c f.point).card) : a (p j) = (e j).val := by
    change (q (q.symm (e j))).val = (e j).val
    rw [q.apply_symm_apply]
  have hsorted : StrictMono (fun j => a (p j)) := by
    intro i j hij
    change a (p i) < a (p j)
    rw [he,he]
    exact e.strictMono hij
  obtain ⟨i,hi⟩ := exists_nearest c f.point
  obtain ⟨k,hk,hki⟩ := Finset.exists_mem_ne (s := incident c f.point)
    (by have h := f.at_least_three; omega) i
  let rho := dist f.point (c i)
  have hrho : 0 < rho := common_nearest_radius_pos hc hki.symm hi (mem_incident.mp hk)
  refine ⟨⟨p,hsorted,rho,hrho,f.radius i (mem_incident.mpr hi),?_⟩⟩
  intro j
  have hj := (p j).property
  have hne := InteriorFace.site_ne_vertex f hc hj
  have hn : ‖c (p j).val-f.point‖ = rho := by
    rw [← dist_eq_norm,dist_comm]
    exact f.equal_radius (p j).val hj i (mem_incident.mpr hi)
  have hdir := circleMap_circleAngle _ (centerDir_norm hne)
  change c (p j).val = f.point+rho • circleMap (siteAngle c f.point (p j).val)
  rw [siteAngle,hdir,← hn,← self_eq_norm_smul_centerDir hne]
  abel

theorem OrderedCircle.angle_bounds {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f)
    (j : Fin (incident c f.point).card) :
    -Real.pi < siteAngle c f.point (o.order j).val ∧
      siteAngle c f.point (o.order j).val ≤ Real.pi :=
  circleAngle_mem_Ioc _

theorem OrderedCircle.actual_sectors {c : Fin 11 → Point} {r : ℝ}
    {f : InteriorFace c r} (o : OrderedCircle c r f) (hc : Function.Injective c)
    (j : Fin (incident c f.point).card) :
    (StrictNormalCone c f.point (o.order j).val).Nonempty ∧
      IsOpen (StrictNormalCone c f.point (o.order j).val) :=
  ⟨⟨c (o.order j).val-f.point,radial_mem_strictNormalCone hc (o.order j).property⟩,
    strictNormalCone_open _ _ _⟩

end N11Formalization.ActualIncidentPolygonOrder
#check @N11Formalization.ActualIncidentPolygonOrder.InteriorFace.orderedCircle
#check @N11Formalization.ActualIncidentPolygonOrder.OrderedCircle.actual_sectors
#print axioms N11Formalization.ActualIncidentPolygonOrder.InteriorFace.orderedCircle
#print axioms N11Formalization.ActualIncidentPolygonOrder.OrderedCircle.actual_sectors
