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

-- def product_to_pullback_diagram (F :(Discrete WalkingPair) ⥤ D) : WalkingCospan ⥤ D := by
--   have left_to_terminal := terminal.from (F.obj ⟨WalkingPair.left⟩)
--   have right_to_terminal := terminal.from (F.obj ⟨WalkingPair.right⟩)
--   exact cospan left_to_terminal right_to_terminal

-- def product_into_pullback_inclusion :(Discrete WalkingPair) ⥤ WalkingCospan :=
--   pair WalkingCospan.left WalkingCospan.right

-- lemma product_pullback_factorization (F :(Discrete WalkingPair) ⥤ D)
--   :F = product_into_pullback_inclusion ⋙ product_to_pullback_diagram F := by
--   let G := product_into_pullback_inclusion ⋙ product_to_pullback_diagram F
--   have h :F =G := sorry
--   apply Prefunctor.ext at h

-- instance CategoryTheory.Limits.hasBinaryProducts_of_hasPullbacks
--      : HasBinaryProducts.{v, u} D where
--       has_limit(F :(Discrete WalkingPair)⥤ D) :HasLimit F := by
--         apply HasLimit.mk
--         let left_to_terminal := terminal.from (F.obj ⟨WalkingPair.left⟩)
--         let right_to_terminal := terminal.from (F.obj ⟨WalkingPair.right⟩)
--         let G := cospan left_to_terminal right_to_terminal
--         let ⟨G_cone, G_cone_is_limit⟩ := getLimitCone G
--         constructor
--         swap
--         constructor
--         swap
--         exact G_cone.pt
--         constructor
--         swap
--         intro j
--         exact G_cone.π.app ((pair WalkingCospan.left WalkingCospan.right).obj j)
--         -- rcases j with ⟨WalkingPair.left| WalkingPair.right⟩
end has_producst_of_has_pullbacks
