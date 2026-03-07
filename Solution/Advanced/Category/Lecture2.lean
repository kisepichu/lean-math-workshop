import Solution.Advanced.Category.Lecture1
import Mathlib.RingTheory.TensorProduct.Maps

namespace Tutorial

open Category

namespace Category

universe u v

variable {C : Type u} [Category.{u, v} C]

/- # 始対象 -/

/-- `a`が始対象とは、任意の`b`について`a`から`b`への射が一意に存在するときをいう。 -/
structure Initial (a : C) where
  /-- 射の族: 各`b : C`について`a`から`b`への射 -/
  fromInitial : ∀ b : C, Hom a b
  /-- 射の族の一意性 -/
  uniq : ∀ {b : C}, ∀ f : Hom a b, f = fromInitial b

/- `Initial a`は性質ではなく構造として定義している。すなわち、単に射の族が存在するというだけでなく、
射の族データも保持している。これは実装の便宜上の都合である。射の族は一意であるため、数学的な違いは
ないと思ってもらって構わない。 -/

/-- 始対象からの射がふたつ存在すれば、それらは等しい。 -/
theorem Initial.uniq' {a : C} (h : Initial a) {b : C} (f g : Hom a b) : f = g :=
  calc f = h.fromInitial b := by /- sorry -/ rw [h.uniq f]
       _ = g := by /- sorry -/ rw [h.uniq g]

end Category

/- # 始対象の例 -/

/-- 空集合は集合の圏における始対象である。 -/
-- 正確には、「空型は型の圏における始対象である。」
-- Leanにおける型と一般的な数学書における集合はほとんど同じ意味です。
example : Initial Empty where
  fromInitial X := by
    intro x
    -- ヒント: 空写像は`Empty.elim`で表される。`apply Empty.elim`を試してみよう。
    -- sorry
    apply Empty.elim x
    -- sorry
  uniq := by
    intro X f
    funext x
    -- ヒント: 空写像のコドメインは命題でもよい（空虚な真）
    -- sorry
    apply Empty.elim x
    -- sorry

/-- 整数環`ℤ`は可換環の圏における始対象である。 -/
/- 環とは底集合と環構造の組であった。底集合`ℤ`に対して、`inferInstance`がmathlibのどこかで定義されて
いる適切な環構造を探してくれている。 -/
example : Initial (⟨ℤ, inferInstance⟩ : CommRingCat) where
  fromInitial := fun R ↦ Int.castRingHom R
  uniq := RingHom.eq_intCast'

/- # 余極限 -/

/- 圏論における重要な構成である**余極限**を定義する。余極限は図式に対して定まる圏の対象である。
図式とは、関手の別名である。関手はまだ定義していなかったので、ここで定義しておく。-/

/- もちろん**極限**も同様に定義できるが、このチュートリアルでは余極限のみ扱う。-/

universe u₁ v₁ u₂ v₂

/-- 圏`C`から圏`D`への関手`F`は対象の間の写像`F.obj : C → D`と射の間の
写像`F.map : Hom a b → Hom (F.obj a) (F.obj b)`の組であって、恒等射と合成を保つものである。 -/
structure Functor (C : Type u₁) [Category.{u₁, v₁} C] (D : Type u₂) [Category.{u₂, v₂} D] where
  obj : C → D
  map : ∀ {a b}, Hom a b → Hom (obj a) (obj b)
  map_id : ∀ a, map (𝟙 a) = 𝟙 (obj a)
  map_comp : ∀ {a b c} (f : Hom a b) (g : Hom b c), map (f ≫ g) = (map f) ≫ (map g)

/- 公理の等式をsimp補題に設定しておく -/
attribute [simp] Functor.map_id Functor.map_comp

/- 余極限とは、普遍性を持つ**余錐**のことである。まずは余錐を定義する。-/

variable {J : Type u₁} [Category.{u₁, v₁} J] {C : Type u₂} [Category.{u₂, v₂} C]

/-- 関手`F`上の余錐 -/
structure Cocone (F : Functor J C) where
  /-- `C`の対象（頂点という） -/
  vertex : C
  /-- 頂点への射の族 -/
  toVertex : ∀ j : J, Hom (F.obj j) vertex
  /-- 射の族の自然性 -/
  naturality : ∀ {i j : J} (f : Hom i j), F.map f ≫ toVertex j = toVertex i

/- 余錐全体は圏を成す。射の集合は次のように定義される。-/

variable {F : Functor J C}

/-- 余錐の間の射 -/
@[ext]
structure CoconeHom (s t : Cocone F) where
  /-- 頂点の間の射 -/
  hom : Hom s.vertex t.vertex
  /-- `hom`と余錐の射は可換 -/
  comm : ∀ j : J, s.toVertex j ≫ hom = t.toVertex j

/-- 余錐全体は圏を成す。 -/
instance : Category (Cocone F) where
  Hom s t := CoconeHom s t
  comp {r s t} (f : CoconeHom r s) (g : CoconeHom s t) := {
    hom := f.hom ≫ g.hom
    comm := by
      intro j
      calc r.toVertex j ≫ f.hom ≫ g.hom
        _ = (r.toVertex j ≫ f.hom) ≫ g.hom := by /- sorry -/ simp
        _ = s.toVertex j ≫ g.hom := by /- sorry -/ rw [f.comm j]
        _ = t.toVertex j := by /- sorry -/ rw [g.comm j]
  }
  id t := {
    hom := 𝟙 t.vertex
    comm := by /- sorry -/ simp
  }

/- これで余極限を定義する準備が整った。余極限は普遍性を持つ余錐であると述べたが、ここでいう普遍性とは
始対象のことである。-/

/-- 余極限とは、余錐の圏での始対象のこと。 -/
def Colimit {F : Functor J C} (t : Cocone F) := Initial t

/- 図式を取り換えるごとに様々な余極限が考えられる。以下では余積とコイコライザーについて考える。 -/

/- # 余積 -/

namespace Coproduct

/- 余積の図式とは、2元集合からの関手である。 -/

/- 2元集合は帰納型として定義される。帰納型は`inductive`コマンドで定義することができる。
帰納型の詳細については https://aconite-ac.github.io/theorem_proving_in_lean4_ja/inductive_types.html
を参照せよ。-/

/-- 2元集合 `{l, r}` -/
inductive Shape : Type
  | l : Shape
  | r : Shape

/- 2元集合を、恒等射のみを持つ圏とみなす。「射の型」の定義にも帰納型を使おう。 -/

/-- `Shape`上の射。恒等射のみを持つ。 -/
inductive ShapeHom : Shape → Shape → Type
  -- 各`i : Shape`について`i`から`i`への射
  | id : ∀ i : Shape, ShapeHom i i

instance : Category Shape where
  Hom i j := ShapeHom i j
  id i := match i with
    /- `match`構文によるパターンマッチを用いた定義。`.l`は`Shape.l`の略。 -/
    | .l => ShapeHom.id .l
    | .r => ShapeHom.id .r
  comp {i j k} _ _ := match i, j, k with
    /- 再びパターンマッチを用いる。ここはLeanが賢くて、空集合から元をとっているケース
    を書かずに済んでいる -/
    | .l, .l, .l => ShapeHom.id .l
    | .r, .r, .r => ShapeHom.id .r
  /- `<;>`でtacticを繋げて場合分けの証明をコンパクトに行うことができる -/
  id_comp := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  comp_id := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  assoc := by rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ ⟨l⟩ ⟨f⟩ ⟨g⟩ ⟨h⟩ <;> rfl

@[simp]
theorem shapeHom_id {i : Shape} : ShapeHom.id i = 𝟙 i := match i with
 | .l => rfl
 | .r => rfl

end Coproduct

/- # 余積の例 -/

/- 圏`Type`での余積はdisjoint unionである。Leanではsum typeとも呼ばれる。`A`と`B`のsum typeを
`A ⊕ B`と書く。sum typeには標準的な写像`Sum.inl : A → A ⊕ B`, `Sum.inr : B → A ⊕ B`が付随する。 -/

/-- 直和を頂点に持つ余錐 -/
@[simps]
def sumCocone (F : Functor Coproduct.Shape Type) : Cocone F where
  vertex := F.obj .l ⊕ F.obj .r
  toVertex j := match j with
    -- 「標準的な写像」を使おう
    | .l => /- sorry -/ Sum.inl
    | .r => /- sorry -/ Sum.inr
  naturality f := match f with
    | .id _ => by
      -- sorry
      simp
      -- sorry

/- 集合の圏における余積はdisjoint union -/
example (F : Functor Coproduct.Shape Type) : Colimit (sumCocone F) where
  fromInitial t := {
    hom := fun x ↦ match x with
      -- `Cocone.toVertex`を使う
      | .inl x => /- sorry -/ Cocone.toVertex t .l x
      | .inr x => /- sorry -/ Cocone.toVertex t .r x
    comm := by
      intro j
      -- `.l`か`.r`で場合分け
      rcases j with _ | _
      · /- sorry -/ rfl
      · /- sorry -/ rfl
  }
  uniq := by
    intro t f
    apply CoconeHom.ext
    funext x
    -- `.inl`か`.inr`で場合分け
    rcases x with x | x
    -- `f = g`のとき`f x = g x`という事実を使いたい場合は、`congrFun`を使うとよい。
    · /- sorry -/ apply congrFun (f.comm .l)
    · /- sorry -/ apply congrFun (f.comm .r)

section TensorProduct

variable {R : CommRingCat}

/- 圏`CommAlgCat R`での余積はテンソル積である。`A`と`B`のテンソル積を`A ⊗[R] B`と書く。
また`a : A`と`b : B`に対して`a ⊗ₜ[R] b`で対応する`A ⊗[R] B`の元を表す。
テンソル積には標準的な写像
* `Algebra.TensorProduct.includeLeft : A →ₐ[R] (A ⊗[R] B)`
* `Algebra.TensorProduct.includeRight : B →ₐ[R] (A ⊗[R] B)`
が付随する。ここで、`→ₐ[R]`は`AlgHom`を表す記号である。 -/

/- おまじない。テンソル積の記号が使えるようになる。 -/
open scoped TensorProduct

/-- テンソル積を頂点に持つ余錐 -/
@[simps! vertex_base toVertex]
def tensorCocone (F : Functor Coproduct.Shape (CommAlgCat R)) : Cocone F where
  vertex := ⟨(F.obj .l) ⊗[R] (F.obj .r), inferInstance, inferInstance⟩
  toVertex := fun j ↦ match j with
    -- ヒント: 「標準的な写像」を使おう
    | .l => /- sorry -/ Algebra.TensorProduct.includeLeft
    | .r => /- sorry -/ Algebra.TensorProduct.includeRight
  naturality := by
    -- `rintro`は`intro`と`rcases`を合わせたtacticである（1行短く書ける）
    rintro i j ⟨_⟩
    -- ヒント: `simp`を試してみよう
    -- sorry
    simp
    -- sorry

/- `R`上の可換代数の圏における余積はテンソル積 -/
example (F : Functor Coproduct.Shape (CommAlgCat R)) : Colimit (tensorCocone F) where
  fromInitial t := {
    -- ヒント: `Algebra.TensorProduct.productMap`を使う
    hom := /- sorry -/ Algebra.TensorProduct.productMap (t.toVertex .l) (t.toVertex .r)
    comm := by
      rintro (_ | _)
      · dsimp only [Hom_def, tensorCocone_toVertex, comp_def, tensorCocone_vertex_base]
        -- ヒント: `apply?`を試してみよう
        -- sorry
        apply Algebra.TensorProduct.productMap_left
        -- sorry
      · dsimp only [Hom_def, tensorCocone_toVertex, comp_def, tensorCocone_vertex_base]
        -- sorry
        apply Algebra.TensorProduct.productMap_right
        -- sorry
  }
  uniq := by
    intro t f
    apply CoconeHom.ext
    have hₗ : ∀ a : F.obj .l, f.hom (a ⊗ₜ[R] 1) = t.toVertex .l a := by
      -- ヒント: `AlgHom.congr_fun`を使う
      -- sorry
      apply AlgHom.congr_fun (f.comm .l)
      -- sorry
    have hᵣ : ∀ b : (F.obj .r), f.hom (1 ⊗ₜ[R] b) = t.toVertex .r b := by
      -- sorry
      apply AlgHom.congr_fun (f.comm .r)
      -- sorry
    apply Algebra.TensorProduct.ext'
    intro a b
    change f.hom (a ⊗ₜ[R] b) = _
    have hab : f.hom (a ⊗ₜ[R] b) = f.hom (a ⊗ₜ[R.base] 1) * f.hom (1 ⊗ₜ[R.base] b) := by
      calc f.hom (a ⊗ₜ[R] b) = f.hom ((a * 1) ⊗ₜ[R] (1 * b)) := by /- sorry -/ simp
      _ = f.hom (a ⊗ₜ[R.base] 1 * 1 ⊗ₜ[R.base] b) := by
        apply congrArg
        show (a * 1) ⊗ₜ[R] (1 * b) = a ⊗ₜ[R] 1 * 1 ⊗ₜ[R] b
        -- ヒント: `apply?`もしくは`rw?`を試してみよう
        -- sorry
        exact (Algebra.TensorProduct.tmul_mul_tmul a 1 1 b).symm
        -- sorry
      _ = f.hom (a ⊗ₜ[R] 1) * f.hom (1 ⊗ₜ[R] b) := by
        apply map_mul
    -- sorry
    rw [hab]
    simp [← hₗ a, ← hᵣ b]
    -- sorry

end TensorProduct

/- # コイコライザー -/

namespace Coequalizer

/- まずはコイコライザーの図式を定義する。コイコライザーの図式とは以下の圏からの関手である。
* 対象: `src`, `tar`
* 射: `src`から`tar`へのふたつの射`fst`, `snd`
```
src ---- fst, snd ----> tar
```
-/

/- これをLeanで書くと次のようになる -/

inductive Shape : Type
  | src : Shape
  | tar : Shape

inductive ShapeHom : Shape → Shape → Type
  | fst : ShapeHom .src .tar
  | snd : ShapeHom .src .tar
  | id (x : Shape) : ShapeHom x x

/- 合成と恒等射はパターンマッチで定義する -/

instance : Category Shape where
  Hom i j := ShapeHom i j
  comp {i j k} f g := match i, j, k with
    | .src, .src, .src => ShapeHom.id .src
    | .tar, .tar, .tar => ShapeHom.id .tar
    | .src, .tar, .tar => f
    | .src, .src, .tar => g
  id i := match i with
    | .src => ShapeHom.id .src
    | .tar => ShapeHom.id .tar
  id_comp := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  comp_id := by rintro ⟨i⟩ ⟨j⟩ ⟨f⟩ <;> rfl
  assoc := by rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ ⟨l⟩ ⟨f⟩ ⟨g⟩ ⟨h⟩ <;> rfl

@[simp]
theorem hom_id {i : Shape} : ShapeHom.id i = 𝟙 i := by cases i <;> rfl

end Coequalizer

/- # コイコライザーの例 -/

/- 圏`Type`でのコイコライザーについて考える。図式`F : Functor Coequalizer.Shape Type`に対して
* `X := F.obj .src`
* `Y := F.obj .tar`
* `f := F.map .fst`
* `g := F.map .snd`
とおいて、`∼`を「任意の`x : X`について`f x ∼ g x`」で生成される同値関係としたとき、商集合`Y / ∼`が
`F`のコイコライザーとなる。-/

/- 「生成される同値関係」は帰納型を使ってシンプルに定義できる -/

inductive CoequalizerRel {X Y : Type} (f g : X → Y) : Y → Y → Prop
  | rel : ∀ x : X, CoequalizerRel f g (f x) (g x)

/- （正確にはこれは「生成される二項関係」であるが、商をとったら同じになるので違いは気にしないでおく） -/

/- Leanにおいて商集合は`Quot`型で表される。二項関係`r : X → X → Prop`が与えられたとき、`Quot r`は
`r`で生成される同値関係で`X`を割った集合を表す。 -/

/- 商集合を作るときに使う -/
#check Quot

/- 商集合の元を作るときに使う -/
#check Quot.mk

/- 商集合からの写像を作るときに使う -/
#check Quot.lift

/- 商集合の元に関する性質を示すときに使う -/
#check Quot.ind

/- 商の公理: 2項関係で関係するふたつの元は、商をとると等しくなる -/
#check Quot.sound

/-- 商集合を頂点に持つ余錐 -/
@[simps]
def quotCocone (F : Functor Coequalizer.Shape Type) : Cocone F where
  -- `Quot`を使う
  vertex := Quot (CoequalizerRel (F.map .fst) (F.map .snd))
  toVertex := fun j => match j with
    -- `Quot.mk`を使う
    | .src => fun x ↦ Quot.mk _ (F.map .fst x)
    | .tar => fun x ↦ Quot.mk _ x
  naturality := by
    rintro (_ | _) (_ | _) ⟨_⟩
    · /- sorry -/ simp
    · /- sorry -/ rfl
    · symm
      funext x
      -- `Quot.sound`を使う
      -- sorry
      apply Quot.sound
      apply CoequalizerRel.rel
      -- sorry
    · /- sorry -/ simp

example (F : Functor Coequalizer.Shape Type) : Colimit (quotCocone F) where
  fromInitial t := {
    -- `Quot.lift`を使う
    hom := Quot.lift (t.toVertex .tar) <| by
      intro x₁ x₂ ⟨x⟩
      have h₁ : t.toVertex .tar (F.map .fst x) = t.toVertex .src x := by
        -- sorry
        apply congrFun (t.naturality .fst)
        -- sorry
      have h₂ : t.toVertex .tar (F.map .snd x) = t.toVertex .src x := by
        -- sorry
        apply congrFun (t.naturality .snd)
        -- sorry
      -- sorry
      rw [h₁, h₂]
      -- sorry
    comm := by
      intro j
      funext x
      cases j
      · /- sorry -/ apply congrFun (t.naturality .fst)
      · /- sorry -/ rfl
  }
  uniq := by
    intro t f
    apply CoconeHom.ext
    funext x
    -- `Quot.ind`を使う。`apply Quot.ind _ x`のように使うとよい。
    -- sorry
    apply Quot.ind _ x
    intro y
    apply congrFun (f.comm .tar) y
    -- sorry

end Tutorial
