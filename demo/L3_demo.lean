import Mathlib

/-!
# AI4Math — Lecture 3: Inductive Types, Quotients, Sets & Functions
Liu Peixuan · SUSTech Math Department

本轮以最新上传稿为底本：只增补正文注释；所有可执行代码保持不变。
[MD] 表示原 Markdown 正文的精简提要；[原稿措辞] 与现有澄清分开标记。

建议环境：Lean 4.19.0 + mathlib v4.19.0（项目已固定版本）。
运行：在本目录执行 `lake exe cache get`，然后 `lake env lean AI4Math_Demo.lean`。
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

open scoped BigOperators
universe u v

namespace MyNat
def foo : ℕ → ℕ := fun n => n + 1
end MyNat

-- #eval ((1:ℕ ).foo) false
-- but when we replace MyNat with Nat, it works

namespace AI4MathDemo

/-! ## A1. 归纳类型：构造子、递归、归纳 -/
namespace InductiveDemo

-- BEGIN tree
inductive Tree (α : Type u) : Type u where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
-- END tree

-- 每个值来自某个构造子。参数 α 在整个类型中固定。
#check Tree.leaf
#check Tree.node
#check Tree.rec

-- BEGIN mirror
def mirror {α : Type u} : Tree α → Tree α
  | .leaf a => .leaf a
  | .node l r => .node (mirror r) (mirror l)
-- END mirror

-- 递归的每次调用都落在直接子树，Lean 可检查终止性。
def nodeCount {α : Type u} : Tree α → Nat
  | .leaf _ => 1
  | .node l r => nodeCount l + nodeCount r + 1

def sampleTree : Tree Nat := .node (.leaf 1) (.node (.leaf 2) (.leaf 3))
#eval nodeCount sampleTree             -- 5
#eval nodeCount (mirror sampleTree)    -- 5

example : mirror (Tree.node (Tree.leaf 1) (Tree.leaf 2)) =
    Tree.node (Tree.leaf 2) (Tree.leaf 1) := rfl

-- BEGIN mirror_proof
theorem mirror_mirror {α : Type u} (t : Tree α) :
    mirror (mirror t) = t := by
  induction t with
  | leaf a => rfl
  | node l r ihL ihR =>
      simp only [mirror, ihL, ihR]
-- END mirror_proof

-- `cases` 只有分情况；`induction` 还提供 ihL、ihR。
theorem nodeCount_mirror {α : Type u} (t : Tree α) :
    nodeCount (mirror t) = nodeCount t := by
  induction t with
  | leaf a => rfl
  | node l r ihL ihR =>
      simp [mirror, nodeCount, ihL, ihR, Nat.add_comm]

-- 构造子不相交；node 在其参数上单射。
example {α : Type u} (a : α) (l r : Tree α) :
    Tree.leaf a ≠ Tree.node l r := by
  intro h
  cases h

example {α : Type u} (l₁ r₁ l₂ r₂ : Tree α)
    (h : Tree.node l₁ r₁ = Tree.node l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  cases h
  exact ⟨rfl, rfl⟩

-- 严格正性：下面的定义不被允许；保留为注释，不破坏文件编译。
-- inductive Bad where
--   | mk : (Bad → Nat) → Bad
-- Bad 出现在构造子参数类型的箭头左侧，是负出现。

/-! ## A2. 索引归纳族：长度进入类型 -/
-- BEGIN vec
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

def Vec.head {α : Type u} {n : Nat} : Vec α (n + 1) → α
  | .cons a _ => a
-- END vec

example : Vec.head (Vec.cons 7 (Vec.cons 9 Vec.nil)) = 7 := rfl
-- 没有 nil 分支：输入类型已经排除了长度为 0 的情形。

/-! ## A3. 归纳命题：构造证据 -/
inductive EvenN : Nat → Prop where
  | zero : EvenN 0
  | step {n : Nat} : EvenN n → EvenN (n + 2)

example : EvenN 4 := EvenN.step (EvenN.step EvenN.zero)

theorem evenN_two_mul (n : Nat) : EvenN (2 * n) := by
  induction n with
  | zero => exact EvenN.zero
  | succ n ih => simpa [Nat.mul_succ] using EvenN.step ih

#print axioms mirror_mirror
end InductiveDemo

/-! ## A4. 商类型：模 2 等价关系 -/
namespace QuotientDemo

-- BEGIN setoid
def modTwo : Setoid Nat where
  r a b := a % 2 = b % 2
  iseqv := ⟨fun _ => rfl,
    fun h => h.symm,
    fun h₁ h₂ => h₁.trans h₂⟩

abbrev Parity := Quotient modTwo

def cls (n : Nat) : Parity := Quotient.mk modTwo n
-- END setoid

-- BEGIN quotient_equality
theorem two_eq_four : cls 2 = cls 4 :=
  Quotient.sound (show 2 % 2 = 4 % 2 from by decide)

example (a b : Nat) (h : cls a = cls b) : a % 2 = b % 2 :=
  Quotient.exact h
-- END quotient_equality

-- sound: a ~ b -> [a] = [b]；exact: 对 Setoid 的商有反向蕴含。
-- 注意：cls 2 与 cls 4 不是通过归约变成同一个代表元；不要用 rfl。

-- BEGIN quotient_lift
def residue : Parity → Nat :=
  Quotient.lift (fun n => n % 2)
    (by intro a b h; exact h)

example (n : Nat) : residue (cls n) = n % 2 := rfl
example : residue (cls 7) = 1 := rfl
-- END quotient_lift

-- lift 的证明义务：改变代表元不能改变输出。
-- BEGIN quotient_induction
theorem residue_lt_two (q : Parity) : residue q < 2 := by
  refine Quotient.inductionOn q ?_
  intro n
  exact Nat.mod_lt n (by decide)
-- END quotient_induction

-- [补充] 商类型上的操作：后继保持模 2 同余。
def next : Parity → Parity :=
  Quotient.lift (fun n => cls (n + 1)) (by
    intro a b h
    apply Quotient.sound
    change (a + 1) % 2 = (b + 1) % 2
    change a % 2 = b % 2 at h
    simp [Nat.add_mod, h])

example : next (cls 2) = cls 3 := rfl

theorem parity_cases (q : Parity) : q = cls 0 ∨ q = cls 1 := by
  refine Quotient.inductionOn q ?_
  intro n
  have hbound : n % 2 < 2 := Nat.mod_lt n (by decide)
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hcases with h0 | h1
  · left
    apply Quotient.sound
    exact h0
  · right
    apply Quotient.sound
    exact h1

-- BEGIN bad_lift
-- 不可能有一个函数把“每个代表元原样取回”。
theorem no_preserving_representative :
    ¬ ∃ f : Parity → Nat, ∀ n, f (cls n) = n := by
  rintro ⟨f, hf⟩
  have h := congrArg f two_eq_four
  rw [hf 2, hf 4] at h
  omega
-- END bad_lift

-- 这不排除选择规范代表元：residue 恰好选择 0 或 1。
-- 但它不能同时让 f [2] = 2 和 f [4] = 4。
-- Quot r 可从任意关系出发；Quotient s 要求 Setoid。
-- 任意关系的 Quot 会识别其生成的等价关系，而不是让商的等号失去等价性。

#print axioms two_eq_four
#print axioms residue_lt_two
end QuotientDemo

/-!
# B. Sets & Functions.md 的 Lean 内容
保留原稿章节顺序；所有修正均用 [修正] 标出。
原文件另存于 ../sources/Sets_Functions_original.md；最新上传底本见 ../sources/latest_user_demo.lean。
-/
namespace SetsFunctions

/-!
[MD 1 / 1.1 — Sets & Functions; Introduction to Set Theory]
Sets and functions: basic language for constructing mathematical concepts.
Collection choices: ordered / unordered; finite / potentially infinite;
multiplicity retained / discarded; predicate / explicit enumeration.
Original terminology: List, Multiset, Finset, Set, Subtype, Fintype.
Keywords below follow the Markdown's chapter order, not a new syllabus.
-/

noncomputable section

/-! ## B1.1.1 List（原稿代码块 01–02） -/

/-!
[MD 1.1.1 — List α]
Definition: ordered, finite; all elements of type α; duplicates allowed.
Order-sensitive: [1, 1, 2] ≠ [1, 2, 1]; constructor: cons (`::`).
Operations: ++, head?, tail, map, filter, foldl/foldr, reverse, membership.
Checks: length, isEmpty; List.range n enumerates 0, ..., n-1.
Notation: ordinary application / dot notation / placeholder `·`.
Original margin keyword: 单子性; no further explanation in the Markdown.
-/

namespace Lists
example : List ℕ := [1, 2, 3]
example : List ℕ := 0 :: [1, 2, 3]
example : [1, 2] ++ [3, 4] = [1, 2, 3, 4] := rfl
example : [1, 2, 3].head? = some 1 := rfl
example : [1, 2, 3].tail = [2, 3] := rfl
example : [1, 2, 3].map (fun x => x + 1) = [2, 3, 4] := rfl
example : [1, 2, 3, 4].filter (· > 2) = [3, 4] := rfl
example : [1, 2, 3].foldl (fun acc x => acc + x) 0 = 6 := rfl
example : [1, 2, 3].foldr (fun x acc => x :: acc) [] = [1, 2, 3] := rfl
example : [1, 2, 3].length = 3 := rfl
example : [1, 2, 3].isEmpty = false := rfl
example : [1, 2, 3].reverse = [3, 2, 1] := rfl
example : 2 ∈ [1, 2, 3] := by simp
example : 4 ∉ [1, 2, 3] := by simp
example : List.range 3 = [0, 1, 2] := rfl

-- [修正] 原稿 List.filter 的普通调用把列表与谓词位置写反；顶层演示加 #eval。
#eval List.filter (fun x : Nat => x > 2) [1, 2, 3, 4]
#eval [1, 2, 3, 4].filter (fun x => x > 2)

-- [修正] “fun x => ... == · > 2” 是解释性文字，不是可直接执行的顶层命令。
-- 下式明确比较两个函数；`·` 是匿名函数语法，而不是运算对象。
example : (fun x : Nat => x > 2) = (· > (2 : Nat)) := rfl
end Lists

/-! ## B1.1.2 Multiset（原稿代码块 03–04） -/

/-!
[MD 1.1.2 — Multiset α]
Definition: unordered, finite; duplicates retained.
Equality depends on multiplicities: {1, 1, 2} = {1, 2, 1}.
Construction: quotient of List α by permutation (List.Perm / List.isSetoid).
Keywords: card counts duplicates; count; filter; map; dedup.
Source's foundational note: no higher inductive types (HITs) used here;
quotient support is a kernel primitive. For an arbitrary relation, the
identified pairs include the equivalence relation it generates.
Connection to A4: respect the relation when defining functions on a quotient.
-/

namespace Multisets
-- [修正] 原稿 def Multiset / def List.isSetoid 是库定义的展示，并包含省略号。
-- 不要重新定义已导入的同名常量；改为查看定义。
#print Multiset
#print List.isSetoid
-- 数学上：Multiset α 是 List α 按排列等价取商。

example : ({1, 1, 2} : Multiset ℕ).card = 3 := rfl
example : ({1, 1, 2} ∩ {1, 2, 2} : Multiset ℕ) = {1, 2} := by decide
example : 1 ∈ ({1, 2, 2} : Multiset ℕ) := by simp
example : ({1, 2, 2, 2} : Multiset ℕ).count 2 = 3 := by decide
example : ({1, 1, 2, 3} : Multiset ℕ).filter (· > 1) = {2, 3} := by decide
example : ({1, 2, 3} : Multiset ℕ).map (· + 1) = {2, 3, 4} := by decide
example : ({1, 1, 2} : Multiset ℕ).dedup = {1, 2} := by decide
-- [补充] 顺序被忽略，重数仍然保留。
example : ({1, 1, 2} : Multiset ℕ) = {2, 1, 1} := by decide
example : ({1, 1, 2} : Multiset ℕ) ≠ {1, 2} := by decide
end Multisets

/-! ## B1.1.3 Finset（原稿代码块 05） -/

/-!
[MD 1.1.3 — Finset α]
Definition: unordered finite collection of distinct elements.
Duplicates discarded: {1, 1, 2} = {1, 2}.
Keywords: union, intersection, difference, membership, range, Icc, powerset.
Contrast with Set α: an arbitrary predicate does not itself supply an enumeration.
[原稿措辞] The Markdown says an explicit Fintype instance is required.
[现有文件的澄清] This is not a requirement on the whole ambient type α;
explicit enumeration or a proof of finiteness can construct a finite subset.
The existing examples and correction notes below are retained unchanged.
-/

namespace Finsets
-- Finset α = 一个无重复的 Multiset α（携带 Nodup 证明）。
-- [修正] 构造有限子集不要求整个 α 有 Fintype；例如 Finset Nat 完全正常。
-- 显式枚举、Finset.range、或 Set.Finite.toFinset 都是构造途径。
example : ({1, 2} ∪ {2, 3} : Finset ℕ) = {1, 2, 3} := by decide
example : ({1, 2} ∩ {2, 3} : Finset ℕ) = {2} := by decide
example : ({1, 2, 3} \ {2} : Finset ℕ) = {1, 3} := by decide
example : 2 ∈ ({1, 2, 3} : Finset ℕ) := by simp
example : 4 ∉ ({1, 2, 3} : Finset ℕ) := by simp
example : Finset.range 3 = {0, 1, 2} := by decide
example : Finset.Icc 2 4 = {2, 3, 4} := by decide
example : ({1, 2} : Finset ℕ).powerset = {∅, {1}, {2}, {1, 2}} := by decide
example : ({1, 1, 2} : Finset ℕ) = {1, 2} := by decide
end Finsets

/-! ## B1.1.4 Set（原稿代码块 06） -/

/-!
[MD 1.1.4 — Set α]
Definition: a predicate α → Prop; elements have the same ambient type.
Potentially infinite; set-builder notation: {n : ℕ | n ≥ 4}.
Membership: applying the predicate to an element.
Union / intersection / difference correspond to ∨ / ∧ / ∧ ¬.
Used as a type, a set gives the subtype of elements satisfying membership.
-/

namespace Sets
def largeNats : Set ℕ := {n | n ≥ 4}
def evens : Set ℕ := {n | n % 2 = 0}
def primes : Set ℕ := {n | Nat.Prime n}

example : largeNats ∪ evens = {n | n ≥ 4 ∨ n % 2 = 0} := rfl
example : largeNats ∩ evens = {n | n ≥ 4 ∧ n % 2 = 0} := rfl
example : largeNats \ primes = {n | n ≥ 4 ∧ ¬ Nat.Prime n} := rfl
-- Set α 是 α → Prop；在类型位置写 s，可被解释为 {x // x ∈ s}。
end Sets

/-! ## B1.1.5 Subtype（原稿代码块 07–08） -/

/-!
[MD 1.1.5 — {x : α // P x}]
Definition: a value x : α together with evidence of P x.
A new type, not merely a predicate; the original and subtype are distinct types.
Construction: ⟨value, proof⟩; projections: .val and .property.
For underlying arithmetic, coerce back to α: (x : ℕ), (x : ℚ).
No arbitrary inherited arithmetic structure is assumed.
Examples from the prose: naturals ≥ 4; rationals ≥ 4; prime naturals.
Your removal of the earlier a/b/c arithmetic examples is preserved.
-/

namespace Subtypes
def nat_ge4 : Type := {n : ℕ // n ≥ 4}
def Rat_ge4 : Type := {n : ℚ // n ≥ 4}
def PrimeNat : Type := {n : ℕ // Nat.Prime n}
#check nat_ge4
#check Rat_ge4
#check PrimeNat



def x : {n : ℕ // 4 ≤ n} := ⟨5, by norm_num⟩
example : (x : ℕ) + 6 = 11 := rfl

def y : {n : ℕ // Nat.Prime n} := ⟨5, by norm_num⟩
example : (y : ℕ) + 6 = 11 := rfl
#check x.val
#check x.property
end Subtypes

/-! ## B1.1.6 Fintype（原稿代码块 09） -/

/-!
[MD 1.1.6 — Fintype α]
Data: a Finset enumeration containing every element of α.
Not a proposition: carries enumeration data; nevertheless a subsingleton
(any two instances of Fintype α are equal).
Finset.univ: the Finset of all elements, using a Fintype α instance.
Existing-file distinction: Finite α states finiteness; Fintype α supplies data.
Examples: bounded-natural subtypes; an equivalence with Fin (k + 1).
-/

namespace FiniteTypes
-- [补充] 显式等价，说明“有限”数据来自哪里，而不依赖隐藏实例搜索。
def leNatEquivFin (k : Nat) : {n : Nat // n ≤ k} ≃ Fin (k + 1) where
  toFun n := ⟨n.val, Nat.lt_succ_of_le n.property⟩
  invFun n := ⟨n.val, Nat.le_of_lt_succ n.is_lt⟩
  left_inv n := by cases n; rfl
  right_inv n := by cases n; rfl

noncomputable instance : Fintype {n : ℕ // n ≤ 4} :=
  Fintype.ofEquiv (Fin 5) (leNatEquivFin 4).symm
noncomputable instance : Fintype {n : ℕ // n ≤ 7} :=
  Fintype.ofEquiv (Fin 8) (leNatEquivFin 7).symm

-- 原稿 `Fintype.ofFinite` 的写法也需要先能获得对应的 Finite 实例。
-- Fintype 携带枚举数据；Finite 只是命题。Finset.univ 需要 Fintype。
#check (Finset.univ : Finset {n : ℕ // n ≤ 4})
end FiniteTypes

/-! ## B1.2.1 Set.Finite（原稿代码块 10） -/

/-!
[MD 1.2 / 1.2.1 — Set Theory Operations; finite sets]
A finite set has its element subtype in bijection with Fin n, for some n.
From a finiteness proof: obtain Fintype data using classical choice.
Set.Finite.toFinset: turn a finite Set into an enumerated Finset.
Closure properties in the examples: subset, intersection, union, powerset.
Keep the distinctions: Set α / the subtype of its members / its finiteness proof.
-/

namespace FiniteSets
example : ({1, 2, 3} : Set ℕ).Finite := by simp
example : ({n : ℕ | n = 1 ∨ n = 2}).Finite := by
  rw [Set.setOf_or]
  exact (Set.finite_singleton 1).union (Set.finite_singleton 2)

example (A B : Set ℕ) [Fintype A] [Fintype B] : (A ∩ B).Finite :=
  (Set.toFinite A).subset Set.inter_subset_left

example (S T : Set ℕ) (h : S ⊆ T) (hT : T.Finite) : S.Finite := hT.subset h

example (A B : Set ℕ) [Fintype A] [Fintype B] : (A ∪ B).Finite :=
  (Set.toFinite A).union (Set.toFinite B)

example (S : Set ℕ) [Fintype S] : (𝒫 S).Finite := (Set.toFinite S).powerset

-- [补充] 从有限性证明取得可枚举有限集；这一般是非计算性的选择。
noncomputable def enumerate (s : Set ℕ) (hs : s.Finite) : Finset ℕ := hs.toFinset
example (s : Set ℕ) (hs : s.Finite) (n : ℕ) :
    n ∈ enumerate s hs ↔ n ∈ s := by simp [enumerate]
end FiniteSets

/-! ## B1.2.2 Cardinality（原稿代码块 11） -/

/-!
[MD 1.2.2 — Cardinality]
Finset.card: number of distinct elements in a finite collection.
Fintype.card: size of a finite type; includes a finite set's subtype.
Multiset.card: counts multiplicities.
Set.ncard: natural-valued cardinality; junk value 0 for an infinite set.
Examples: range, union, Cartesian product, Fin n, function types, filtering.
Finite function types: |α → β| = |β| ^ |α|; here |Fin 2 → Fin 3| = 9.
-/

namespace Cardinalities
example : Finset.card (Finset.range 5) = 5 := Finset.card_range 5
example : Finset.card (({1, 2, 3} : Finset ℕ) ∪ {3, 4}) = 4 := by decide
example : Finset.card (({1, 2} : Finset ℕ) ×ˢ ({3, 4} : Finset ℕ)) = 4 := by decide
example : Fintype.card (Fin 5) = 5 := Fintype.card_fin 5

-- [修正/展开] 用 // 明确写出 Subtype；展示与 Fin 5 的等价。
def ltNatEquivFin (k : Nat) : {n : Nat // n < k} ≃ Fin k where
  toFun n := ⟨n.val, n.property⟩
  invFun n := ⟨n.val, n.isLt⟩
  left_inv n := by cases n; rfl
  right_inv n := by cases n; rfl

noncomputable instance : Fintype {n : ℕ // n < 5} :=
  Fintype.ofEquiv (Fin 5) (ltNatEquivFin 5).symm

example : Fintype.card {n : ℕ // n < 5} = 5 := by
  simpa using Fintype.card_congr (ltNatEquivFin 5)

example : Fintype.card (Fin 2 → Fin 3) = 9 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  norm_num

example : ({1, 1, 2, 3} : Multiset ℕ).card = 4 := rfl
example : ({1, 2, 2} + {2, 3} : Multiset ℕ).card = 5 := rfl
example : (({1, 1, 2, 3} : Multiset ℕ).filter (· > 1)).card = 2 := by decide
example : ({1, 2, 3} : Set ℕ).ncard = 3 := by norm_num
example : ({5} : Set ℕ).ncard = 1 := by simp

-- [修正] 原稿把类型类 hA : Finite A 直接当成 A.Finite 传入。
-- 用 Set.toFinite A 得到该定理要求的集合有限性证明。
example (A B : Set ℕ) [Finite A] : (A ∩ B).ncard ≤ A.ncard := by
  exact Set.ncard_inter_le_ncard_left A B (Set.toFinite A)
end Cardinalities

/-! ## B1.2.3 Sum and Prod（原稿代码块 12） -/

/-!
[MD 1.2.3 — Sum and Prod]
Finset.sum / Finset.prod: finite aggregation with additive / multiplicative structure.
Multiset.sum / Multiset.prod: multiplicities contribute repeatedly.
Keywords: union, Cartesian product, filtering, geometric series.
tsum / tprod: infinite aggregation; convergence matters for intended series semantics.
[原稿措辞] The Markdown says a Set must first be converted to Finset.
[现有文件的澄清] This applies to finite Finset aggregation, not all sums:
a tsum can be indexed by the subtype of a set. See the retained example below.
-/

namespace SumsProducts
example : (Finset.range 5).sum id = 10 := by decide
example : ({1, 2, 3} : Finset ℕ).sum (fun x => x ^ 2) = 14 := by decide
example : (({1, 2} : Finset ℕ) ∪ {3}).sum id = 6 := by decide
example : (Finset.range 5).prod (fun x => x + 1) = 120 := by decide
example : ({2, 3, 4} : Finset ℕ).prod id = 24 := by decide
example : (({1, 2} : Finset ℕ) ×ˢ ({3, 4} : Finset ℕ)).sum
    (fun p => p.1 + p.2) = 20 := by decide

example : ({1, 1, 2, 3} : Multiset ℕ).sum = 7 := rfl
example : ({1, 2, 2} + {2, 3} : Multiset ℕ).sum = 10 := rfl
example : ({2, 2, 3} : Multiset ℕ).prod = 12 := rfl
example : (({1, 2, 2, 3} : Multiset ℕ).filter (· > 1)).sum = 7 := by decide
example : (({1, 2, 2, 3} : Multiset ℕ).filter (· > 1)).prod = 12 := by decide

example : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 := by
  simpa using tsum_geometric_two

-- [修正说明] Finset.sum 要求有限枚举；但不能说 Set “不能求和”。
-- 集合上的无限和可以写作对子类型的 tsum，例如下面只是查看其类型。
#check (∑' n : {n : ℕ // n ≥ 4}, ((1 : ℝ) / 2) ^ n.val)
-- tsum 是总定义；收敛条件用于保证它与通常的无穷级数语义相符。
end SumsProducts

/-! ## B1.2.4 Max and Min（原稿代码块 13） -/

/-!
[MD 1.2.4 — Max and Min]
Finset.max' / min': linear order plus proof of nonemptiness.
Finset.sup / inf: generalized finite extrema; suitable bottom / top for empty sets.
sSup / sInf: set supremum / infimum in the appropriate order structure.
IsGreatest s a: membership plus an upper bound; IsLeast: the lower-bound analogue.
[原稿笔误] IsLeast is described as "greatest" in the source; the existing file
already flags this and uses the least-element formulation.
Source also lists Multiset.max/min and Multiset.sup/inf.
[原稿 API 提示] Its blanket Option-valued description of Multiset.max/min is
not asserted by the current demo; retain the existing version-sensitive warning.
-/

namespace MaxMin
example : ({3, 1, 4} : Finset ℕ).max' (by simp) = 4 := by decide
example : (Finset.Icc 5 10).max' (by simp) = 10 := by decide
example : ({3, 1, 4} : Finset ℕ).min' (by simp) = 1 := by decide
example : (Finset.Icc 5 10).min' (by simp) = 5 := by decide
example : ({3, 1, 4} : Finset ℕ).sup id = 4 := by decide
example : (∅ : Finset ℕ).sup id = 0 := rfl

-- [展开] 明确证明最大／最小，再取条件完备格上的上／下确界。
-- [修正] IsLeast 指最小元，原稿英文误写成 greatest。
theorem greatest_four : IsGreatest ({3, 1, 4} : Set ℕ) 4 := by
  constructor
  · simp
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num

theorem least_one : IsLeast ({3, 1, 4} : Set ℕ) 1 := by
  constructor
  · simp
  · intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num

example : sSup ({3, 1, 4} : Set ℕ) = 4 :=
  greatest_four.isLUB.csSup_eq ⟨4, greatest_four.1⟩
example : sInf ({3, 1, 4} : Set ℕ) = 1 :=
  least_one.isGLB.csInf_eq ⟨1, least_one.1⟩
example : IsGreatest ({3, 1, 4} : Set ℕ) 4 := greatest_four
example : IsLeast ({3, 1, 4} : Set ℕ) 1 := least_one
-- [修正] 原稿在 sInf/IsLeast 示例中混写 Finset 与 Set；这里统一为 Set。
-- 不演示原稿文字中的 “Multiset.max 返回 Option”：那不是此环境可假定的统一 API。
end MaxMin

/-! ## B1.3 Function Basic（原稿代码块 14–15） -/

/-!
[MD 1.3 — Function Basic]
Type: f : α → β; application: f a (no parentheses required).
Examples: ℕ → ℕ; Fin 3 → ℕ; ℚ → ℝ; functions between product types.
Subtype inputs require a value with membership evidence: ⟨value, proof⟩.
Subtype outputs may need coercion back to the ambient type for arithmetic.
[原稿措辞] The prose says Lean does not explicitly define domain/codomain.
[现有文件的澄清] α and β already specify them; an image/range is a separate notion.
The source's output-≥4, output+3=5 claim is impossible; your existing
counterstatement is retained, not replaced with an unrelated function.
-/

namespace Functions
section
variable (f1 : ℕ → ℕ) (f2 : Fin 3 → ℕ) (f3 : ℚ → ℝ)
variable (f4 : Fin 3 × Fin 4 → ℝ × ℚ)
#check f1
#check f2
#check f3
#check f4
end

-- [修正] 原稿：(f ⟨1, ...⟩ : Nat) + 3 = 5，且 f 的输出 ≥ 4。
-- 该命题并非“对任意 f 缺证明”，而是必然为假：左边 ≥ 7。
example (f : {n : ℕ // n ≤ 4} → {n : ℕ // n ≥ 4}) :
    7 ≤ (f ⟨1, by norm_num⟩ : ℕ) + 3 := by
  have h := (f ⟨1, by norm_num⟩).property
  change 4 ≤ (f ⟨1, by norm_num⟩ : ℕ) at h
  omega

example (f : {n : ℕ // n ≤ 4} → {n : ℕ // n ≥ 4}) :
    ¬ ((f ⟨1, by norm_num⟩ : ℕ) + 3 = 5) := by
  have h := (f ⟨1, by norm_num⟩).property
  change 4 ≤ (f ⟨1, by norm_num⟩ : ℕ) at h
  omega

-- [补充] 若要算出固定值，应提供具体函数。
def addFour (n : {n : ℕ // n ≤ 4}) : {n : ℕ // n ≥ 4} :=
  ⟨n.val + 4, by omega⟩
example : (addFour ⟨1, by norm_num⟩ : ℕ) + 3 = 8 := rfl
-- 域和值域就在 α → β 的类型中；“实际像集”则是另一回事。
end Functions

/-! ## B1.4.1 Injective / Surjective / Bijective（原稿代码块 16） -/

/-!
[MD 1.4 / 1.4.1 — Function Operations]
Injective: f a = f b → a = b (distinct inputs have distinct outputs).
Surjective: ∀ y, ∃ x, f x = y (every codomain element has a preimage).
Bijective: Injective f ∧ Surjective f (exactly one preimage for each output).
Proof patterns: introduce two inputs / choose a preimage / split a conjunction.
Examples: identity, n ↦ n + 1, x ↦ 2*x over ℝ, composition of injections.
-/

namespace FunctionOperations
example : Function.Injective (id : ℕ → ℕ) := Function.injective_id

lemma f_plus_1_inj (f : ℕ → ℕ) (hf : ∀ n, f n = n + 1) :
    Function.Injective f := by
  intro a b h
  rw [hf, hf] at h
  omega

example : Function.Surjective (id : ℕ → ℕ) := Function.surjective_id

lemma f_mul_2_surj (f : ℝ → ℝ) (hf : ∀ n, f n = 2 * n) :
    Function.Surjective f := by
  intro b
  refine ⟨b / 2, ?_⟩
  rw [hf]
  ring

example : Function.Bijective (id : ℕ → ℕ) := Function.bijective_id

lemma f_mul_2_bij (f : ℝ → ℝ) (hf : ∀ n, f n = 2 * n) :
    Function.Bijective f := by
  constructor
  · intro a b h
    rw [hf, hf] at h
    linarith
  · exact f_mul_2_surj f hf

example (f : ℕ → ℤ) (g : ℤ → ℚ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := hg.comp hf

/-! ## B1.4.2 Inverse / Composition / Identity（原稿代码块 17） -/

/-!
[MD 1.4.2 — Inverse, Composition, Identity]
For a bijection f : A → B, its inverse g satisfies g (f a) = a and f (g b) = b.
Composition: (f ∘ g) x = f (g x); identity: id x = x.
[原稿记号与现有澄清] The mathematical inverse notation f⁻¹ must not be confused
with Lean's pointwise inverse on ℝ → ℝ: (g⁻¹) x = (g x)⁻¹.
Function.invFun: choice-based inverse candidate; hypotheses still needed.
Existing supplement: Equiv packages forward map, inverse map, and both laws.
-/

section
variable (g : ℝ → ℝ)
#check g⁻¹
-- [重要修正] 对 ℝ → ℝ，这里的 g⁻¹ 是逐点倒数：x ↦ (g x)⁻¹。
-- 它不是“函数的复合逆”。
example (x : ℝ) : (g⁻¹) x = (g x)⁻¹ := rfl

variable (h1 : ℝ → ℝ) (h2 : ℚ → ℝ)
#check h1 ∘ h2
#check (id : ℚ → ℚ)
#check Function.invFun (fun x : ℝ => 2 * x)
-- invFun 使用选择；要证明它是逆函数，还需相应单射／满射性质。
end

-- [补充] 用 Equiv 明确打包双射及双侧逆。
def doubleEquiv : ℝ ≃ ℝ where
  toFun x := 2 * x
  invFun x := x / 2
  left_inv x := by dsimp; ring
  right_inv x := by dsimp; ring

example (x : ℝ) : doubleEquiv.symm (doubleEquiv x) = x :=
  doubleEquiv.symm_apply_apply x
end FunctionOperations

/-! ## B1.5.1 Odd and Even（原稿代码块 18–19） -/

/-!
[MD 1.5 / 1.5.1 — Function Properties; odd/even]
Even: f (-x) = f x; graph symmetric about the y-axis.
Odd: f (-x) = -f x; graph symmetric about the origin.
Examples: x^(2*n) and x^(2*n+1); Lean: Function.Even / Function.Odd.
Sum: even+even → even; odd+odd → odd; mixed sum: no general parity.
Product: even*even → even; odd*odd → even; odd*even → odd.
All displayed algebraic examples below are real-valued functions.
-/

namespace FunctionProperties
lemma x_pow_2n_even (n : ℕ) : Function.Even (fun x : ℝ => x ^ (2 * n)) := by
  intro a
  exact (even_two_mul n).neg_pow a

lemma x_pow_2n_plus_1_odd (n : ℕ) :
    Function.Odd (fun x : ℝ => x ^ (2 * n + 1)) := by
  intro a
  exact (odd_two_mul_add_one n).neg_pow a

lemma Odd_Sum (f g : ℝ → ℝ) (hf : Function.Odd f) (hg : Function.Odd g) :
    Function.Odd (f + g) := hf.add hg
lemma Even_Sum (f g : ℝ → ℝ) (hf : Function.Even f) (hg : Function.Even g) :
    Function.Even (f + g) := hf.add hg
lemma Even_mul_Even (f g : ℝ → ℝ) (hf : Function.Even f) (hg : Function.Even g) :
    Function.Even (f * g) := hf.mul_even hg
lemma Odd_mul_Odd (f g : ℝ → ℝ) (hf : Function.Odd f) (hg : Function.Odd g) :
    Function.Even (f * g) := hf.mul_odd hg
-- [修正] 原稿名字 Old_mul_Even 中 Old 是拼写错误，改为 Odd。
lemma Odd_mul_Even (f g : ℝ → ℝ) (hf : Function.Odd f) (hg : Function.Even g) :
    Function.Odd (f * g) := hf.mul_even hg
lemma Even_mul_Odd (f g : ℝ → ℝ) (hf : Function.Even f) (hg : Function.Odd g) :
    Function.Odd (f * g) := hf.mul_odd hg

/-! ## B1.5.2 Monotonicity（原稿代码块 20–21） -/

/-!
[MD 1.5.2 — Monotonicity]
Increasing / nondecreasing: x₁ ≤ x₂ → f x₁ ≤ f x₂; StrictMono uses < on both sides.
Decreasing / nonincreasing: reverse the output inequality; StrictAnti is strict.
For real-valued functions: decreasing iff -f is increasing.
Monotone f: entire domain; MonotoneOn f s: restricted to members of s.
Closure: sum; increasing-after-increasing composition; nonnegative increasing product.
[原稿与代码] The prose assumes positive factors; the retained lemma only needs ≥ 0.
Composition signs: increasing∘decreasing → decreasing;
decreasing∘decreasing → increasing. Track the order of g ∘ f.
-/

lemma prove_Increasing (f : ℝ → ℝ)
    (h : ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂) : Monotone f := by
  intro x₁ x₂ hx
  exact h x₁ x₂ hx

lemma prove_StrictlyIncreasing (f : ℝ → ℝ)
    (h : ∀ x₁ x₂, x₁ < x₂ → f x₁ < f x₂) : StrictMono f := by
  intro x₁ x₂ hx
  exact h x₁ x₂ hx

lemma prove_Decreasing (f : ℝ → ℝ)
    (h : ∀ x₁ x₂, x₁ ≤ x₂ → f x₂ ≤ f x₁) : Antitone f := by
  intro x₁ x₂ hx
  exact h x₁ x₂ hx

lemma prove_StrictlyDecreasing (f : ℝ → ℝ)
    (h : ∀ x₁ x₂, x₁ < x₂ → f x₂ < f x₁) : StrictAnti f := by
  intro x₁ x₂ hx
  exact h x₁ x₂ hx

lemma Increasing_Sum (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g) :
    Monotone (f + g) := by
  intro x₁ x₂ hx
  exact add_le_add (hf hx) (hg hx)

lemma IncreasingPos_mul_IncreasingPos (f g : ℝ → ℝ)
    (hf : Monotone f) (hg : Monotone g)
    (hf_pos : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 ≤ g x) : Monotone (f * g) := by
  intro x₁ x₂ hx
  exact mul_le_mul (hf hx) (hg hx) (hg_pos x₁) (hf_pos x₂)

lemma Increasing_comp_Increasing (f g : ℝ → ℝ)
    (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) := hg.comp hf
lemma Increasing_comp_Decreasing (f g : ℝ → ℝ)
    (hf : Antitone f) (hg : Monotone g) : Antitone (g ∘ f) := hg.comp_antitone hf
lemma Decreasing_comp_Decreasing (f g : ℝ → ℝ)
    (hf : Antitone f) (hg : Antitone g) : Monotone (g ∘ f) := hg.comp hf

/-! ## B1.5.3 Periodicity（原稿代码块 22–23） -/

/-!
[MD 1.5.3 — Periodicity]
Classical statement: f (x + T) = f x for a positive period T.
Fundamental period: the least positive period, if one exists.
[现有文件的澄清] Function.Periodic f T itself neither requires T > 0
nor asserts a least positive period.
Examples: sin/cos with 2*π; tan with π.
Integer translations: f (x + n*T) = f x for n : ℤ.
Product: two functions with period T give a product with the same period.
Antiperiodic: f (x + T) = -f x ⇒ f (x + 2*T) = f x.
-/

lemma periodic_function {α : Type u} {β : Type v} [Add α]
    (f : α → β) (c : α) (hf : ∀ x, f (x + c) = f x) : Function.Periodic f c := hf

example : Function.Periodic Real.sin (2 * Real.pi) := Real.sin_periodic
example : Function.Periodic Real.cos (2 * Real.pi) := Real.cos_periodic
example : Function.Periodic Real.tan Real.pi := Real.tan_periodic
-- [澄清] Function.Periodic 本身不要求周期正，也不保证存在最小正周期。

lemma periodic_translation_int {f : ℝ → ℝ} {T : ℝ}
    (hf : Function.Periodic f T) (n : ℤ) (x : ℝ) :
    f (x + n * T) = f x := by
  exact hf.int_mul n x

lemma periodic_mul' {f g : ℝ → ℝ} {T : ℝ}
    (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    Function.Periodic (f * g) T := by
  intro x
  simp only [Pi.mul_apply, hf x, hg x]

lemma antiperiodic_implies_periodic {f : ℝ → ℝ} {T : ℝ}
    (hanti : Function.Antiperiodic f T) : Function.Periodic f (2 * T) :=
  hanti.periodic_two_mul
end FunctionProperties

end
end SetsFunctions
end AI4MathDemo
