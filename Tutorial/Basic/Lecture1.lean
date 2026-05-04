import Batteries

/- # 遊び方 -/

-- 証明があるべき場所に`sorry`と書いてあるので...
example : 1 + 1 = 2 := by
  simp

-- 正しい証明に書き直そう！
example : 1 + 1 = 2 := by
  trivial

/- # Leanにおける論理
数学的に意味のある文を**命題**と呼ぶ。例えば、「1 + 1 = 2」「3は偶数である」「リーマン予想」などが
命題である。命題は真である場合もあれば偽である場合もあるし、真偽がわかっていない場合もある。数学の
教科書などでは「命題」という単語は「定理」という単語の別名として使われることもあるが、ここでは違う
意味で使われていることに注意しよう。

`P`が命題であることをLeanでは`P : Prop`と書く。また、`h : P`と書けば`h`が`P`の証明であることを
意味する。別の言い方をすると、`h : P`は`P`が真であり、その事実に`h`と名前を付けているという
こともできる。
-/

/-
Leanで証明を書くためのコマンドを**tactic**と呼ぶ。このファイルでは以下のtacticについて学ぶ

- `apply`
- `intro`
- `constructor`
- `cases`

-/

/- # ならば
Leanでは「ならば」を`→`で表す。例えば「PならばQ」は`P → Q`と書く。記号`→`を出すには`\to`もしくは
`\r`と入力する。VSCode上で`→`の上にカーソルを乗せると入力の仕方が表示される。
-/

-- 以下`P, Q, R`は命題とする。
variable (P Q R : Prop)

example (hP : P) : P := by
  -- ヒント: `apply hP`と入力すれば仮定をゴールに適用できる。
  apply hP

example (h : P → Q) (hP : P) : Q := by
  -- 改行して複数のtacticを並べることもできる。インデント（行の頭の空白の個数）を
  -- 揃える必要があることに注意しよう。
  -- ヒント: `apply`を2回使う。
  apply (h hP)

example (h : P → Q) (hP : P) : Q :=
  h hP

example (hPtoQ : P → Q) (hQtoR : Q → R) : P → R := by
  -- 導出図の一番下 P → R からだんだん上に作っていく
  intro hP -- →I を使って解消される仮定 P を取り出し R をゴールにする
  apply hQtoR -- →E を使って左上に Q→R の証明を置き右上の Q をゴールにする
  apply hPtoQ -- →E を使って左上に P→Q の証明を置き右上の P をゴールにする
  apply hP -- 完了 (→E? を使って左上に (無→)P の証明を置くとゴールは無になる)

-- 項 λa:A.b : 命題 A→B を、 A の証明を受け取って B の証明を返すもの考えられる。または、

example (hPtoQ : P → Q) (hQtoR : Q → R) : P → R := by
  intro hP
  apply hQtoR
  apply (hPtoQ hP) -- P

-- λa:A.b : 型   A→B を、 A を受け取って B を返す関数として考えられる。

example (hPtoQ : P → Q) (hQtoR : Q → R) : P → R := by
  apply fun hP ↦ hQtoR (hPtoQ hP)

-- by apply は消せる

example (f : P → Q) (g : Q → R) : P → R :=
  fun x ↦ g (f x)

-- TIPS: 入力した`intro`や`apply`の上にカーソルを乗せるとtacticの説明が表示される。

/- # 否定
否定命題`¬P`は`P → False`として定義される。
-/

example (hP : P) (hP' : ¬P) : False := by
  -- ヒント: 否定命題も`apply`することができる。
  apply (hP' hP)

example (hP : P) (hP' : ¬P) : False :=
  hP' hP


example : (P → Q) → ¬Q → ¬P := by
  intro hPtoQ
  intro hQtoFalse
  intro hP
  apply (hQtoFalse (hPtoQ hP))

example : (P → Q) → ¬Q → ¬P :=
  fun fpq ↦ fun fqb ↦ fun p ↦ fqb (fpq p)

-- 下から →I で取ったものに名前を付けている感じか
-- 複数行で書くときは apply は →E で、適用後と関数を使って引数だけにする感じ
-- 関数の方も上に続く場合は必ず λ 項っぽく書くんかな
-- そうでないときは複数行で書けば括弧をなくせるのか


example : ¬¬¬P → ¬P := by
  intro hNNNP
  intro hP
  apply hNNNP
  intro hPtoFalse
  apply (hPtoFalse hP)

-- 最初はいちいち λ 項で考えないとわからなかったが慣れてきた
-- 導出図をイメージしながらやる

/- # 偽
偽命題`False`からは任意の命題が証明できる。この事実には`False.elim`という名前がついている。
-/

example : False → P := by
  apply False.elim
-- その型を持つ項として言語に用意されている感じか

example (h : ¬P) : P → Q := by
  intro hP
  apply False.elim
  apply (h hP)

/- # かつ
「PかつQ」は`P ∧ Q`と書かれる。`P ∧ Q`を示したい場合、`constructor`を用いれば右画面に表示される
ゴールが`P`と`Q`のそれぞれを示すふたつのゴールに分岐する。
-/

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- `constructor`によってゴールが分岐する。分岐したゴールたちには名前がついていて、`case`を使って
  -- それぞれのゴールに的を絞ることができる。
  constructor
  case left =>
    apply hP
  case right =>
    apply hQ

example (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨hP, hQ⟩

example (hP : P) (hQ : Q) : P ∧ Q := by
  -- 別の書き方: `·`を用いた箇条書きでも分岐したでもそれぞれのゴールに的を絞ることができる。
  constructor
  · apply hP
  · apply hQ

/- # かつ
仮定`h : P ∧ Q`を持っているとき、`h.left`で`P`の証明を、`h.right`で`Q`の証明を得ることができる。
-/

example : P ∧ Q → P := by
  intro h
  apply h.left

example : P ∧ Q → P :=
  fun h ↦ h.left

example : P ∧ Q → Q := by
  intro h
  apply h.right

example : P ∧ Q → Q :=
  fun h ↦ h.right

example : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · apply h.right
  · apply h.left

example : P ∧ Q → Q ∧ P :=
  fun h ↦ ⟨h.right, h.left⟩


/- # または
「PまたはQ」は`P ∨ Q`と書かれる。仮定`h : P ∨ Q`を持っているとき、`cases h`によって場合分けの
証明を行える。
-/

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  -- `cases h`によって右画面に新しいゴール`inl`と`inr`が現れる。
  -- (これらの名前はinsert leftとinsert rightの略らしい)
  cases h
  -- `case inl hP`で左側の命題`P`の証明に`hP`という名前を付けている。
  case inl hP =>
    sorry
  case inr hQ =>
    sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hPR hQR
  -- `rcases`という`cases`の別バージョンがある。ひとつの違いとして、こちらは`case`を使わなくても
  -- 分岐した仮定に名前を付けられる。箇条書きを使いたい人はこちらを使おう。
  rcases h with hP | hQ
  · sorry
  · sorry

example (h : P ∨ Q) : (P → R) → (Q → P) → R := by
  sorry

example : ¬¬P → P := by
  -- `have` tacticで仮定を追加することができる。以降のファイルではヒントとしても用いる。
  have h : P ∨ ¬P := by apply Classical.em
  sorry

/-
最初のチュートリアルファイル`Lecture1.lean`は以上です。
`Lecture2.lean`に進む前に、証明にエラーがないか確認してみましょう。
VS Codeを使っている場合は、エラーが残っているとその箇所に赤線が表示されます。
-/

/- 以下おまけ。スキップして`Lecture2.lean`に進んでも大丈夫です。 -/

-- 連続して`apply`を使うときは...
example (h : P → Q) (h' : Q → R) : P → R := by
  intro hP
  apply h'
  apply h
  apply hP

-- このようにまとめることができる。なぜなら`h : P → Q`と`hP : P`に対して`h hP : Q`だからである。
example (h : P → Q) (h' : Q → R) : P → R := by
  intro hP
  apply h'
  apply h hP

-- さらにまとめられる。
example (h : P → Q) (h' : Q → R) : P → R := by
  intro hP
  apply h' (h hP)

-- さらにさらにまとめられて...
example (h : P → Q) (h' : Q → R) : P → R := by
  apply (fun hP ↦ h' (h hP))

-- 実はこのようにも書ける。簡単な証明が短く書けるのは嬉しい。
example (h : P → Q) (h' : Q → R) : P → R :=
  fun hP ↦ h' (h hP)

-- 面白い事実: 文字を変えると、関数の合成に見える！
example (f : P → Q) (g : Q → R) : P → R :=
  fun x ↦ g (f x)

/-
Leanでは「ならば」を`→`で表す。`⇒`は用いない。実は、Lean内部では命題`P → Q`の項は`P`から`Q`への関数
として解釈される。ここではこれ以上説明しないが、この考え方は**Curry–Howard対応**と呼ばれていて、
Leanで論理を扱う際の基礎となっている。
-/
