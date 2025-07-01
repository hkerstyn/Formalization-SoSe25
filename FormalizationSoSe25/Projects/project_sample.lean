-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

open CategoryTheory
open CategoryTheory.Limits

noncomputable section has_producst_of_has_pullbacks

variable {D: Type u} [Category.{v, u} D] [HasTerminal.{v, u} D] [HasPullbacks.{v, u} D]
  (F :(Discrete WalkingPair) ⥤ D)

def G :WalkingCospan ⥤ D := by
  let left_to_terminal := terminal.from (F.obj ⟨WalkingPair.left⟩)
  let right_to_terminal := terminal.from (F.obj ⟨WalkingPair.right⟩)
  exact cospan left_to_terminal right_to_terminal

def I :(Discrete WalkingPair ⥤ WalkingCospan) :=
  pair WalkingCospan.left WalkingCospan.right

def alpha : F  ≅ (I ⋙ G F) := by
  apply Discrete.natIso
  intro i
  have equality : F.obj i = (I⋙ G F).obj i
  let left_to_terminal := terminal.from (F.obj ⟨WalkingPair.left⟩)
  let right_to_terminal := terminal.from (F.obj ⟨WalkingPair.right⟩)
  simp
  obtain ⟨ left|right⟩ := i
  unfold I
  rw[pair_obj_left]
  unfold G
  rw[<-cospan_left left_to_terminal right_to_terminal]
  rfl
  unfold I
  rw[pair_obj_right]
  unfold G
  rw[<-cospan_right left_to_terminal right_to_terminal]
  rfl
  rw[equality]

def J :Cone F → Cone (G F) := by
  intro cone
  have cone' :BinaryFan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)
  exact (Cones.postcompose (diagramIsoPair F).hom).obj cone
  apply PullbackCone.mk cone'.fst cone'.snd
  aesop_cat

theorem productExists : HasLimit F := by
  let ⟨G_cone, G_cone_is_limit⟩ := getLimitCone (G F)
  let F_cone := (Cones.postcompose (alpha F).inv).obj (G_cone.whisker I)
  apply HasLimit.mk
  constructor
  swap
  exact F_cone
  constructor
  rotate_left 2
  intro cone
  exact G_cone_is_limit.lift (J F cone)
  intro cone ⟨j⟩
  unfold F_cone I alpha
  obtain ⟨left, right⟩ := j
  unfold I J BinaryFan.fst
  simp
  unfold I J BinaryFan.snd
  simp
  intro cone m fac
  rw [<-G_cone_is_limit.uniq]
  intro j
  obtain none| i := j
  aesop_cat
  let fac_i := fac ⟨i⟩
  unfold F_cone I at fac_i
  simp at fac_i
  obtain left|right := i
  unfold J BinaryFan.fst
  simp
  rw[<- fac_i]
  unfold alpha I
  simp
  unfold J
  simp
  unfold BinaryFan.snd
  simp
  rw[<- fac_i]
  unfold alpha I
  simp
end has_producst_of_has_pullbacks

section internal_category_struct
-- Before we define internal categories, we define ICategoryStruct.
-- This contains all the data of an internal category, except associativity
-- and unitality of identities.
class ICategoryStruct (C :Type u) [Category.{v, u} C] where
  -- Objects and morphisms
  objs :C
  homs :C
  source :homs ⟶ objs
  target :homs ⟶ objs
  id :objs ⟶ homs
  -- Composable pairs and triples.
  pair_cone :LimitCone (cospan source target)
  tri_cone :LimitCone (cospan ((PullbackCone.snd pair_cone.cone)≫ source) target)
  comp :pair_cone.cone.pt ⟶ homs
  -- Axioms for source and target.
  source_id : id ≫ source = 𝟙 objs
  target_id : id ≫ target = 𝟙 objs
  source_comp :comp ≫ source = (PullbackCone.snd pair_cone.cone) ≫ source
  target_comp :comp ≫ target = (PullbackCone.fst pair_cone.cone) ≫ target

-- We now prove that for every ICategoryStruct, certain morphisms exist.
-- This is necessary to even be able to formulate the definition of an internal
-- category.
variable {C :Type u} [Category.{v, u} C] {Γ:ICategoryStruct C}
open ICategoryStruct

-- "Composes" two morphisms.
def pcomp {A :C} (f g :A⟶ homs) (comm : f ≫ source = g ≫ target): A⟶ homs := by
  apply (· ≫ comp)
  exact Γ.pair_cone.isLimit.lift (PullbackCone.mk f g comm)

-- Necessary for ICategory.id_comp
def id_comp_hom :Γ.homs ⟶ Γ.homs:= by
  apply pcomp (𝟙 homs) (source ≫ id)
  simp
  rw [target_id]
  simp

-- Necessary for ICategory.comp_id
def comp_id_hom :Γ.homs ⟶Γ.homs:= by
  apply pcomp (target ≫ id) (𝟙 homs)
  simp
  rw [source_id]
  simp

-- Now we define the two morphisms that compose a triple in each possible way.
def π₁₂ :Γ.tri_cone.cone.pt ⟶ Γ.pair_cone.cone.pt := (PullbackCone.fst Γ.tri_cone.cone)
def π₁ :Γ.tri_cone.cone.pt ⟶ Γ.homs := π₁₂ ≫ (PullbackCone.fst Γ.pair_cone.cone)
def π₂ :Γ.tri_cone.cone.pt ⟶ Γ.homs := π₁₂ ≫ (PullbackCone.snd Γ.pair_cone.cone)
def π₃ :Γ.tri_cone.cone.pt ⟶ Γ.homs := (PullbackCone.snd Γ.tri_cone.cone)
def π₂₃ :Γ.tri_cone.cone.pt ⟶ Γ.pair_cone.cone.pt := by
  have comm :π₂ ≫ Γ.source = π₃ ≫ Γ.target
  unfold π₂ π₃ π₁₂
  simp
  exact PullbackCone.condition Γ.tri_cone.cone
  exact Γ.pair_cone.isLimit.lift (PullbackCone.mk π₂ π₃ comm)

def left_comp :Γ.tri_cone.cone.pt ⟶ Γ.homs := by
  apply pcomp (π₁₂≫ comp) π₃
  unfold π₁₂ π₃
  simp
  rw[source_comp, PullbackCone.condition Γ.tri_cone.cone]

def right_comp :Γ.tri_cone.cone.pt ⟶ Γ.homs := by
  apply pcomp π₁ (π₂₃ ≫ comp)
  unfold π₁ π₂₃ π₁₂ π₂ π₃ π₁₂
  simp
  rw[target_comp, PullbackCone.condition Γ.pair_cone.cone]
  simp

end internal_category_struct


section internal_category

class ICategory (C :Type u) [Category.{v,u} C] extends ICategoryStruct C where
  -- Category axioms.
  id_comp :id_comp_hom = 𝟙 homs
  comp_id :comp_id_hom = 𝟙 homs
  assoc :left_comp = right_comp

end internal_category
