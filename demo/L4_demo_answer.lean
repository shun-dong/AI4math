import Mathlib

/-!
# 初等代数 · 按 tactic 组织的 Lean 4 入门（完整证明版）

数学素材主要来自 `Lean4Align/Elementary Algebra.md`，
少量来自 `summercourse/L01.lean`（改写、min、整除）与 `L03.lean`（二元表达式配方）。
Part 5 是另编的 ℚ² 向量练习，包含运算法则、线性相关与线性组合。

结构（一个大节最多 5 个小节）：

* Part 1 基础操作（手工骨架）
  1.1 rw ｜ 1.2 exact / apply ｜ 1.3 intro / constructor / by_cases
  1.4 rcases / obtain / use / have ｜ 1.5 calc
* Part 2 计算（等式与具体值，不用推理）
  2.1 rfl / decide ｜ 2.2 norm_num ｜ 2.3 ring / ring_nf / field_simp / compute_degree!
  2.4 特殊函数与具体值
* Part 3 自动化
  3.1 simp / simp only / unfold ｜ 3.2 linarith ｜ 3.3 omega
  3.4 nlinarith / positivity ｜ 3.5 tauto / exact? / simp?
* Part 4 进阶
  4.1 定义展开与外延性（含同余） ｜ 4.2 多项式 ｜ 4.3 复数 ｜ 4.4 超越函数与三角
* Part 5 ℚ² 向量：运算法则、线性相关与线性组合

使用约定：

* Part 1 把用到的定理全部 `#check` / `#print` 出来，不需要查库；
* Part 2–4 逐步减少提示；
* Part 5 给出向量的定义和常用引理，综合使用前面学过的 tactic。

现场用法：每次只写一条 tactic，停在行末看 InfoView 里的目标变化。
-/

namespace ElementaryAlgebra.Tactics

/-! ## 1.1 rw：把等式当作替换规则

`rw [h]` 把目标里的左端换成右端；`rw [← h]` 反向；`rw [h] at h₂` 改写假设 h₂。
每行只放一条 rw，先说清楚"哪一个子式会被替换"。
-/

#check mul_assoc
#check mul_comm
#check sub_self
#check zero_add
#check add_neg_cancel
#check add_assoc
#check add_zero
#check add_mul
#check one_mul
#check one_add_one_eq_two

-- [1.1.1] 演示（来自 summercourse/L01）：先换 e，再调括号，最后才能用 h₁。
-- 第一次停顿：a * (b * f) 里为什么还不能直接 rw [h₁]？
theorem rw_example (a b c d e f : ℝ)
    (h₁ : a * b = c * d) (h₂ : e = f) :
    a * (b * e) = c * (d * f) := by
  -- @@SOLUTION@@
  rw [h₂]
  rw [← mul_assoc a b f]
  rw [h₁]
  rw [mul_assoc c d f]
  -- @@END@@

-- [1.1.2] 演示：前三步只改假设 hc，主目标不动；第四步才使用整理好的 hc。
example (a b c d e : ℝ) (hc : c = b * a - d) (hd : d = a * b) :
    c + e = e := by
  -- @@SOLUTION@@
  rw [hd] at hc
  rw [mul_comm b a] at hc
  rw [sub_self] at hc
  rw [hc]
  rw [zero_add]
  -- @@END@@

-- [1.1.3] 练习：先消去 b 与 -b，再把 2 * a 展开成两个 a。
-- 想一想：为什么这里要反向使用 1 + 1 = 2？
example (a b : ℝ) : (2 * a + b) + (-b) = a + a := by
  -- @@SOLUTION@@
  rw [add_assoc]
  rw [add_neg_cancel]
  rw [add_zero]
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]
  -- @@END@@

/-! ## 1.2 exact / apply：关闭目标与反向拆目标

`exact h` 交出一个类型正好是目标的证明；
`apply 引理` 用引理的结论匹配目标，把未给出的前提留下当子目标；
每个 `·` 处理一个子目标，缩进表示正在处理哪一层。
-/

#check add_le_add_right
#print add_le_add_right
#check add_le_add_left
#check add_le_add
#check le_trans
#check le_antisymm
#check le_min
#check min_le_left
#check min_le_right
#check dvd_add
#print dvd_add
#check dvd_mul_of_dvd_right
#print dvd_mul_of_dvd_right
#check dvd_mul_right
#check pow_two

-- [1.2.1] 热身：h 的类型就是目标，所以 exact 一步就结束。
example (x y : ℝ) (h : x = y) : x = y := by
  exact h

-- [1.2.2] 短引导：apply 之后，剩下要证的就是 x ≤ y。
example (x y c : ℝ) (h : x ≤ y) : x + c ≤ y + c := by
  -- @@SOLUTION@@
  apply add_le_add_right
  exact h
  -- @@END@@

-- [1.2.3] 重点：外层加法拆成两个目标，内层加法再把第一个目标拆成两个。
-- 第一层是 (a + c) ≤ (b + d) 与 e ≤ f；第二层是 a ≤ b 与 c ≤ d。
-- 注意最后的 exact hef 要退回第一层的缩进。
example (a b c d e f : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) :
    (a + c) + e ≤ (b + d) + f := by
  -- @@SOLUTION@@
  apply add_le_add
  · apply add_le_add
    · exact hab
    · exact hcd
  · exact hef
  -- @@END@@

-- [1.2.4] 重点：不用 min_comm，亲手把 min 的交换律拆成四个小不等式。
-- apply le_antisymm 把等式拆成两个方向；apply le_min 把"≤ 一个最小值"拆成"≤ 两个数"。
theorem min_comm_by_steps (a b : ℝ) : min a b = min b a := by
  -- @@SOLUTION@@
  apply le_antisymm
  · apply le_min
    · exact min_le_right a b
    · exact min_le_left a b
  · apply le_min
    · exact min_le_right b a
    · exact min_le_left b a
  -- @@END@@

#check min_comm_by_steps
#print min_comm_by_steps

-- [1.2.5] 练习（来自 summercourse/L01）：整除。x ∣ t 读作"x 整除 t"。
-- 先按加法拆成三部分，再处理乘法，最后一部分要用到假设 h。
example (x y z w : ℤ) (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  -- @@SOLUTION@@
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      exact dvd_mul_right x z
    · rw [pow_two]
      exact dvd_mul_right x x
  · rw [pow_two]
    apply dvd_mul_of_dvd_right
    exact h
  -- @@END@@

/-! ## 1.3 intro / constructor / by_cases：拆目标的结构

`intro` 把目标里 `→` 左边的条件和 `∀` 的变量搬到上下文；
`constructor` 把 `∧` 拆成两个目标（对 `↔` 则是两个方向）；
`by_cases h : P` 把目标分成 `h : P` 与 `h : ¬P` 两支。
-/

#check Nat.Prime
#check Nat.Prime.two_le
#print Nat.Prime.two_le
#check min_eq_left
#check min_eq_right
#check le_of_not_ge

-- [1.3.1] intro：箭头与全称量词。
example (p : ℕ) : Nat.Prime p → 2 ≤ p := by
  -- @@SOLUTION@@
  intro hp
  exact Nat.Prime.two_le hp
  -- @@END@@

example : ∀ x : ℝ, x + 0 = x := by
  -- @@SOLUTION@@
  intro x
  rw [add_zero]
  -- @@END@@

-- [1.3.2] constructor：拆 ∧ 与 ↔。
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a ∧ 0 ≤ b := by
  -- @@SOLUTION@@
  constructor
  · exact ha
  · exact hb
  -- @@END@@

example (x y : ℝ) : x = y ↔ y = x := by
  -- @@SOLUTION@@
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm
  -- @@END@@

-- [1.3.3] 练习：by_cases 分类讨论。两支各自用一条引理结束。
example (a b : ℝ) : min a b = a ∨ min a b = b := by
  -- @@SOLUTION@@
  by_cases h : a ≤ b
  · left
    exact min_eq_left h
  · right
    exact min_eq_right (le_of_not_ge h)
  -- @@END@@

/-! ## 1.4 rcases / obtain / use / have：拆假设、造见证、留中间结论

`rcases h with ⟨k, hk⟩` 拆假设里的 `∧` 与 `∃`；`rcases h with (h₁ | h₂)` 分 `∨` 的两支；
`use k` 给出 `∃` 的见证；`have h : P := by ...` 先证一条中间事实，再在主证明里用掉。
-/

#check le_antisymm
#check le_trans
#print le_trans
#check add_le_add_right
#print add_le_add_right
#check mul_zero

-- [1.4.1] 拆 ∨：两支的证法不一样，各写各的。
example (n : ℤ) (h : n = 0 ∨ n = 1) : n * (n - 1) = 0 := by
  -- @@SOLUTION@@
  rcases h with h | h
  · rw [h, zero_mul]
  · rw [h, sub_self, mul_zero]
  -- @@END@@

-- [1.4.2] 拆 ∃ 与造 ∃：整除的定义（素材来自源文件 §2.8.1）。
example (a b : ℤ) : a ∣ b ↔ ∃ k, a * k = b := by
  -- @@SOLUTION@@
  constructor
  · intro ha
    rcases ha with ⟨c, hc⟩
    use c
    rw [hc]
  · intro ha
    obtain ⟨k, hk⟩ := ha
    use k
    rw [hk]
  -- @@END@@

-- [1.4.3] 造见证：不用推公式，只要挑一个值并验证（对应源文件 §2.4.3 的多项式根）。
-- 这里的 norm_num 见 2.2。
example : ∃ x : ℝ, x ^ 2 - 3 * x + 2 = 0 := by
  -- @@SOLUTION@@
  use 1
  norm_num
  -- @@END@@

-- [1.4.4] have：先把两条 ≤ 合成一条，再一次性用掉。
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a + 1 ≤ c + 1 := by
  -- @@SOLUTION@@
  have h : a ≤ c := le_trans h₁ h₂
  exact add_le_add_right h 1
  -- @@END@@

-- [1.4.5] 拆 ∧：先给两部分起名字，比在目标里到处写 h.1、h.2 清楚。
example (x y : ℝ) (h : x ≤ y ∧ y ≤ x) : x = y := by
  -- @@SOLUTION@@
  rcases h with ⟨h₁, h₂⟩
  exact le_antisymm h₁ h₂
  -- @@END@@

/-! ## 1.5 calc：组织等式推导与估计

```
calc
  A ≤ B := by ...
  _ = C := by ...
  _ ≤ D := by ...
```
`_` 表示上一行的右端；每一步单独证明，Lean 将它们接成完整推导。
中间式可以保留一部分，只对另一部分进行估计。
等式负责整理表达式，不等式负责得到新的上界。
-/

#check mul_assoc
#check abs_add
#print abs_add
#check abs_mul
#check abs_nonneg
#check le_max_left
#check le_max_right
#check mul_le_mul_of_nonneg_left
#print mul_le_mul_of_nonneg_left
#check add_le_add
#check add_le_add_right
#check add_le_add_left
#check add_mul

-- [1.5.1] 用 calc 重写 [1.1.1]，把每一步的中间式列出来。
theorem calc_example (a b c d e f : ℝ)
    (h₁ : a * b = c * d) (h₂ : e = f) :
    a * (b * e) = c * (d * f) := by
  calc
    a * (b * e) = a * (b * f) := by
      -- @@SOLUTION@@
      rw [h₂]
      -- @@END@@
    _ = (a * b) * f := by
      -- @@SOLUTION@@
      rw [mul_assoc]
      -- @@END@@
    _ = (c * d) * f := by
      -- @@SOLUTION@@
      rw [h₁]
      -- @@END@@
    _ = c * (d * f) := by
      -- @@SOLUTION@@
      rw [mul_assoc]
      -- @@END@@

-- [1.5.2] 用 max |x| |y| 统一控制两个乘积中的因子。
-- 提示：先用三角不等式，再分别估计两项，最后提取公因子。
example (a b x y : ℝ) :
    |a * x + b * y| ≤ (|a| + |b|) * max |x| |y| := by
  calc
    |a * x + b * y| ≤ |a * x| + |b * y| := by
      -- @@SOLUTION@@
      exact abs_add (a * x) (b * y)
      -- @@END@@
    _ = |a| * |x| + |b * y| := by
      -- @@SOLUTION@@
      rw [abs_mul a x]
      -- @@END@@
    _ ≤ |a| * max |x| |y| + |b * y| := by
      -- @@SOLUTION@@
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left (le_max_left |x| |y|) (abs_nonneg a)
      -- @@END@@
    _ = |a| * max |x| |y| + |b| * |y| := by
      -- @@SOLUTION@@
      rw [abs_mul b y]
      -- @@END@@
    _ ≤ |a| * max |x| |y| + |b| * max |x| |y| := by
      -- @@SOLUTION@@
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (le_max_right |x| |y|) (abs_nonneg b)
      -- @@END@@
    _ = (|a| + |b|) * max |x| |y| := by
      -- @@SOLUTION@@
      rw [add_mul]
      -- @@END@@

-- [1.5.3] 三项三角不等式：先把两项的结论存成 h，再用 calc 接上第三项。
-- 第一次用 abs_add 时，两个参数是 a + b 与 c。
example (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  -- @@SOLUTION@@
  have h : |a + b| ≤ |a| + |b| := abs_add a b
  calc
    |a + b + c| ≤ |a + b| + |c| := by
      exact abs_add (a + b) c
    _ ≤ (|a| + |b|) + |c| := by
      exact add_le_add_right h |c|
  -- @@END@@

/-! ## 2.1 rfl / decide：算出来的东西

`#eval` 是把表达式**求值**，它不产生定理；
`rfl` 证的是"两边依定义相等"；
`decide` 用来判定**可以计算**的命题（先算出真假，再把 `true` 变成证明）。
-/

#eval (2 : ℕ) - 5   -- 0：自然数减法截断在零
#eval (2 : ℤ) - 5   -- -3
#eval (2 : ℤ) / 4   -- 0：整数除法
#eval (2 : ℚ) / 4   -- 1/2

#check Nat.factorial
#check Nat.gcd
#check Nat.Prime

-- [2.1.1] rfl：两边依定义就相等。
example : (3 + 4 : ℕ) = 7 := by rfl
example : Nat.factorial 0 = 1 := by rfl
example : Nat.lcm 6 8 = 24 := by rfl

-- [2.1.2] decide：命题可以由计算判定。
example : Nat.gcd 12 18 = 6 := by decide
example : Nat.Prime 17 := by decide
example : ¬ Nat.Prime 1 := by decide

/-! ## 2.2 norm_num：具体数值的等式与不等式

`norm_num` 负责数值计算，也负责把具体数值的等式/不等式证掉。
类型决定运算结果：同一个 `2 / 4` 在 ℤ、ℚ、ℝ 里答案是三件不同的事。
-/

#check Real.sqrt_nonneg

-- [2.2.1] 类型决定结果（素材来自源文件 §2.1.1）。
example : 1 + 2 = 3 := by norm_num
example : (2 : ℤ) / 4 = 0 := by norm_num
example : (5 : ℕ) / 4 = 1 := by norm_num
example : (2 : ℚ) / 4 = 1 / 2 := by norm_num

-- [2.2.2] 具体数值也可以出现在长表达式里。
example : ((11 : ℤ) - 5) ^ 3 = 6 ^ 3 := by norm_num

-- [2.2.3] 根号、绝对值、取整（素材来自源文件 §2.6.2）。
example : Real.sqrt 4 = 2 := by norm_num
example : |(-3 : ℝ)| = 3 := by norm_num
example : ⌊(3.7 : ℝ)⌋ = 3 := by norm_num
example : ⌈(3.1 : ℝ)⌉ = 4 := by norm_num

-- [2.2.4] 结论里带变量时，norm_num 只负责其中的数值步骤。
example (x : ℝ) (h : x ≤ (1 : ℝ) / 3 + 1 / 6) : x < 1 := by
  calc
    x ≤ (1 : ℝ) / 3 + 1 / 6 := h
    _ = 1 / 2 := by norm_num
    _ < 1 := by norm_num

/-! ## 2.3 ring / ring_nf / field_simp / compute_degree!

`ring` 用交换律、结合律、分配律把多项式整理成标准形；
`ring_nf` 是"正规化"版本，能处理带除法与根号的表达式，并把结果写成人能读的形式；
`field_simp` 用非零条件清掉分母；
`compute_degree!` 处理多项式的次数。
-/

#check mul_add
#check sq_nonneg
#print sq_nonneg

-- [2.3.1] ring：对所有变量都成立的恒等式（素材来自源文件 §2.1.2）。
example (n : ℕ) (m : ℤ) : 2 ^ (n + 1) * m = 2 * 2 ^ n * m := by ring
example (a b : ℚ) : (a - b) ^ 3 = a ^ 3 - 3 * a ^ 2 * b + 3 * a * b ^ 2 - b ^ 3 := by ring
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

-- [2.3.2] ring_nf：先看它把目标整理成了什么。
example (x y : ℝ) : (x + y) ^ 2 - (x - y) ^ 2 = 4 * x * y := by ring_nf

-- [2.3.3] 展开定义之后 ring（二元表达式来自 summercourse/L03）。
def algebraExpr (x y : ℝ) : ℝ := x * y - x - y

#check algebraExpr
#print algebraExpr

theorem algebraExpr_factor (x y : ℝ) :
    algebraExpr x y = (x - 1) * (y - 1) - 1 := by
  -- @@SOLUTION@@
  simp only [algebraExpr]
  ring
  -- @@END@@

-- [2.3.4] field_simp：用非零条件消去分母。
example (x : ℝ) (hx : x ≠ 0) : (x ^ 2 + 3 * x) / x = x + 3 := by
  -- @@SOLUTION@@
  field_simp
  ring
  -- @@END@@

-- [2.3.5] compute_degree!：多项式次数的专用自动化（详见 4.2）。
open Polynomial

-- 注意：tactic 不能用 #check 查看，用 #print 看引理、用文档看 tactic。
example : (X ^ 3 + 2 * X ^ 2 + (5 : ℤ[X])).degree = 3 := by compute_degree!

/-! ## 2.4 特殊函数与具体值

源文件 §2.6 的整章几乎都是这一类：阶乘、组合数、gcd/lcm、素性、互素、
totient、取模与数位、绝对值、根号、取整。
它们的共同点是"具体值 = 可以算"，所以 `rfl` / `decide` / `norm_num` 就够了。
-/

#check Nat.factorial
#check Nat.choose
#check Nat.gcd
#check Nat.lcm
#check Nat.Prime
#check Nat.Coprime
#check Nat.totient
#check Nat.ofDigits
#check Real.sqrt
#check Real.rpow

-- 阶乘与组合数
example : Nat.factorial 5 = 120 := by decide
example : Nat.choose 5 2 = 10 := by decide
example : Nat.choose 4 2 + Nat.choose 4 3 = Nat.choose 5 3 := by decide

-- gcd / lcm
example : Nat.lcm 6 8 = 24 := by rfl
example : Nat.gcd 12 18 + Nat.lcm 12 18 = 42 := by decide

-- 素性与互素（注意 Nat.Prime 是 Prop，不是 Bool）
example : Nat.Prime 17 := by decide
example : ¬ Nat.Prime 1 := by decide
example : Nat.Coprime 5 7 := by norm_num

-- 取模与数位（数位列表是低位在前）
example : 17 % 5 = 2 := by decide
example : Nat.totient 10 = 4 := by decide
example : Nat.ofDigits 10 [3, 2, 1] = 123 := by decide
#eval Nat.digits 10 123   -- [3, 2, 1]

-- 实数的绝对值、根号、取整
example : |(-7 : ℝ)| = 7 := by norm_num
example : Real.sqrt 9 = 3 := by norm_num
example : ⌊(5.9 : ℝ)⌋ = 5 := by norm_num

/-! ## 3.1 simp / simp only / unfold

`simp` 反复使用化简规则，直到目标不再变化；
`simp only [...]` 只允许指定的规则，结果可控、可读；
`unfold 定义名` 只展开一个定义，是"最小剂量的 simp"。
-/

#check add_zero
#check mul_one
#check sub_self

-- [3.1.1] simp 一把梭。
example (x y : ℝ) : (x + 0) * 1 + (y - y) = x := by
  -- @@SOLUTION@@
  simp
  -- @@END@@

-- [3.1.2] simp only：自己指定规则。
example (x y : ℝ) : (x + 0) * 1 + (y - y) = x := by
  -- @@SOLUTION@@
  simp only [add_zero, mul_one, sub_self]
  -- @@END@@

-- [3.1.3] 在假设上 simp。
example (a b c : ℝ) (h₁ : a + 0 ≤ b * 1) (h₂ : b + 0 ≤ c) : a ≤ c := by
  -- @@SOLUTION@@
  simp only [add_zero, mul_one] at h₁
  simp only [add_zero] at h₂
  exact le_trans h₁ h₂
  -- @@END@@

-- [3.1.4] unfold：只展开自己写的定义。
def myExpr (x : ℝ) : ℝ := x * x - 1

#check myExpr
#print myExpr

example (x : ℝ) : myExpr x + 1 = x ^ 2 := by
  -- @@SOLUTION@@
  unfold myExpr
  ring
  -- @@END@@

/-! ## 3.2 linarith

`linarith` 组合上下文里的线性等式与不等式；
`linarith [事实]` 还把方括号里的事实交给它用（例如 sq_nonneg x）。
它不会自己去找数学引理，也不会处理非线性的乘积。
-/

#check sq_nonneg
#print sq_nonneg

-- [3.2.1] 上下文已经给出所需的两个方程。
example (a b : ℚ) (h₁ : a + b = 10) (h₂ : a - b = 2) : a = 6 := by
  -- @@SOLUTION@@
  linarith
  -- @@END@@

-- [3.2.2] 三个不等式导出矛盾。
example (x y z : ℚ) (h₁ : 2 * x < 3 * y) (h₂ : -4 * x + 2 * z < 0)
    (h₃ : 12 * y - 4 * z < 0) : False := by
  -- @@SOLUTION@@
  linarith
  -- @@END@@

-- [3.2.3] 重点：只输入 linarith 会失败，因为它不知道 x ^ 2 ≥ 0。
-- 这里把 x ^ 2 当作一个整体 t，推理只需要 0 ≤ t 与 t + y ≤ 3。
example (x y : ℝ) (h : x ^ 2 + y ≤ 3) : y ≤ 3 := by
  -- @@SOLUTION@@
  linarith [sq_nonneg x]
  -- @@END@@

-- [3.2.4] 等价写法：先把事实 have 出来，再交给 linarith。
example (x y : ℝ) (h : x ^ 2 + y ≤ 3) : y ≤ 3 := by
  -- @@SOLUTION@@
  have hsq : 0 ≤ x ^ 2 := sq_nonneg x
  linarith
  -- @@END@@

/-! ## 3.3 omega

`omega` 负责 ℤ 与 ℕ 上的线性算术，还包括整除、取模、截断减法这些
`linarith` 完全不管的东西。凡是"整数性质"参与推理，先试 omega。
-/

-- [3.3.1] 整除（素材来自源文件 §2.1.2）。
example (n : ℤ) : 3 ∣ 6 * n + 12 := by
  -- @@SOLUTION@@
  omega
  -- @@END@@

example : (3 ∣ 123) ∧ (17 ∣ 187) ∧ 13 * 3 + 5 = 44 := by
  -- @@SOLUTION@@
  omega
  -- @@END@@

-- [3.3.2] ℕ 上的截断减法与线性推理。
example (a b : ℕ) (h : a + 5 ≤ b) : a < b := by
  -- @@SOLUTION@@
  omega
  -- @@END@@

example (a b : ℕ) (h : a ≤ b) : a - b = 0 := by
  -- @@SOLUTION@@
  omega
  -- @@END@@

/-! ## 3.4 nlinarith / positivity

`positivity` 专门制造"非负/正"这种前提（平方、绝对值、根号、指数都认识）；
`nlinarith` 是 linarith 的非线性版本：它需要你给一点线索（通常是一个平方非负），
然后自己把多项式展开、配方、加总。慢，而且容易失败，但能一步收掉很多不等式。
-/

#check sq_nonneg
#check Real.sqrt_nonneg
#print Real.sqrt_nonneg

-- [3.4.1] positivity：不必手写 sq_nonneg。
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by
  -- @@SOLUTION@@
  positivity
  -- @@END@@

example (x : ℝ) : 0 ≤ Real.sqrt (x ^ 2 + 1) := by
  -- @@SOLUTION@@
  positivity
  -- @@END@@

-- [3.4.2] nlinarith：给出"线索"后一步完成。
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  -- @@SOLUTION@@
  nlinarith [sq_nonneg (a - b)]
  -- @@END@@

-- [3.4.3] nlinarith 的典型用法：线索给对了就一步收掉。
-- 源文件 §2.3.2 用几十行证的二元 Cauchy–Schwarz，关键是想到 (a * d - b * c) ^ 2 ≥ 0。
example (a b c d : ℝ) :
    (a * b + c * d) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
  -- @@SOLUTION@@
  nlinarith [sq_nonneg (a * d - b * c)]
  -- @@END@@

/-! ## 3.5 tauto / exact? / simp?：让 Lean 自己找，或者告诉你怎么找

`tauto` 解决命题逻辑（∧ ∨ → ¬ ↔）的目标；
`exact?` 在库里搜一条"正好能关闭当前目标"的定理，并在 InfoView 里给出 `Try this: exact ...`；
`simp?` 先做 simp，再告诉你它到底用了哪些规则：`Try this: simp only [...]`，
把这一行拷回来，就是一条可控的、可读的证明。
-/

-- [3.5.1] tauto：命题逻辑。
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  -- @@SOLUTION@@
  tauto
  -- @@END@@

example (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) (h₃ : P) : R := by
  -- @@SOLUTION@@
  tauto
  -- @@END@@

-- [3.5.2] exact? 的威力：不知道引理叫什么，让 Lean 去搜。
-- 把光标停在 exact? 上，InfoView 会给出一行 "Try this: exact mul_comm a b"。
example (a b : ℝ) : a * b = b * a := by
  exact?

-- [3.5.3] simp? 的威力：把"一把梭"变成"可控的 simp only"。
-- InfoView 会给出 "Try this: simp only [add_zero, mul_one, sub_self]"。
example (x y : ℝ) : (x + 0) * 1 + (y - y) = x := by
  -- @@SOLUTION@@
  simp?
  -- @@END@@

/-! ## 4.1 定义展开与外延性（含同余）

`ext x` 把"两个集合相等"变成"逐点比较"；
`unfold` 把定义摊开，露出真正要证的东西；
同余 `a ≡ b [MOD n]` 就是 `a % n = b % n`，它的运算律靠 unfold + rw 完成。
-/

#check Set.ext
#print Set.ext
#check Nat.ModEq
#print Nat.ModEq
#check Nat.modEq_iff_dvd
#print Nat.modEq_iff_dvd
#check Nat.ModEq.mul_left
#check Nat.mul_mod

-- [4.1.1] ext：集合相等 = 逐点等价。
example : ({x : ℝ | x + 0 = 3} : Set ℝ) = {x : ℝ | x = 3} := by
  -- @@SOLUTION@@
  ext x
  simp
  -- @@END@@

-- [4.1.2] 同余的具体值可以直接判定。
example : 17 ≡ 2 [MOD 5] := by
  -- @@SOLUTION@@
  decide
  -- @@END@@

-- [4.1.3] 同余的运算律：unfold 定义之后，看到的就是两个 % 相等（素材来自源文件 §2.8.5）。
theorem modEq_symm (a b n : ℕ) (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := by
  -- @@SOLUTION@@
  unfold Nat.ModEq at *
  exact h.symm
  -- @@END@@

-- [4.1.4] 乘法律：手写这一步要小心"rw 只改第一处匹配"，一不小心就把 % n 叠起来；
-- 这类运算律库里已经写好了，直接调用即可。
theorem modEq_mul_left (a b n c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
  h.mul_left c

/-! ## 4.2 多项式

`Polynomial R[X]` 的相等由系数决定（`Polynomial.ext_iff`）；
系数的运算律大多是现成的 simp 引理（`Polynomial.coeff_add` 等）；
`C` 是常数多项式，`X` 是自变量。
-/

open Polynomial

#check Polynomial.ext_iff
#print Polynomial.ext_iff
#check Polynomial.coeff_add
#print Polynomial.coeff_add
#check Polynomial.coeff_mul

-- [4.2.1] 多项式相等 = 所有系数相等（素材来自源文件 §2.4）。
example (P Q : ℚ[X]) (h : ∀ k, P.coeff k = Q.coeff k) : P = Q := by
  -- @@SOLUTION@@
  rw [Polynomial.ext_iff]
  exact h
  -- @@END@@

-- [4.2.2] 系数公式本来就在库里。
lemma poly_add_coeff {R : Type*} [Semiring R] (P Q : R[X]) (k : ℕ) :
    (P + Q).coeff k = P.coeff k + Q.coeff k := by
  -- @@SOLUTION@@
  simp only [Polynomial.coeff_add]
  -- @@END@@

-- [4.2.3] 具体算一个系数：simp 自己找不到 coeff 1 2 = 0，把两条引理指给它。
example : (X ^ 2 + 1 : ℚ[X]).coeff 2 = 1 := by
  -- @@SOLUTION@@
  simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  -- @@END@@

/-! ## 4.3 复数

复数的证明有一个固定模板（源文件 §2.7 里出现十几次）：

1. `apply Complex.ext_iff.mpr` 把 `z = w` 变成 `z.re = w.re ∧ z.im = w.im`；
2. `constructor` 分成实部、虚部两个目标；
3. 每一支 `simp [投影引理]`（`Complex.add_re`、`Complex.mul_re`、`Complex.conj_re` …）；
4. 需要整理时补一条 `ring`。

补充：`conj` 是 `ComplexConjugate` locale 里的记号，用之前要 `open scoped ComplexConjugate`。
-/

open Complex
open scoped ComplexConjugate

#check Complex.ext_iff
#print Complex.ext_iff
#check Complex.add_re
#check Complex.add_im
#check Complex.mul_re
#check Complex.mul_im
#check Complex.conj_re
#check Complex.conj_im

-- [4.3.1] 模板第一步：加法。
lemma complex_add (a b c d : ℝ) :
    Complex.mk a b + Complex.mk c d = Complex.mk (a + c) (b + d) := by
  -- @@SOLUTION@@
  apply Complex.ext_iff.mpr
  constructor
  · simp [Complex.add_re]
  · simp [Complex.add_im]
  -- @@END@@

-- [4.3.2] 模板第二步：乘法（系数里出现 i² = -1 的效果）。
lemma complex_mul (a b c d : ℝ) :
    Complex.mk a b * Complex.mk c d = Complex.mk (a * c - b * d) (a * d + b * c) := by
  -- @@SOLUTION@@
  apply Complex.ext_iff.mpr
  constructor
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
  -- @@END@@

-- [4.3.3] 练习：共轭与加法可交换。
-- 注意 conj 是 locale 记号（ComplexConjugate），文件开头要 open scoped。
lemma complex_conj_add (z w : ℂ) : conj (z + w) = conj z + conj w := by
  -- @@SOLUTION@@
  apply Complex.ext_iff.mpr
  constructor
  · simp [Complex.add_re, Complex.conj_re]
  · simp [Complex.add_im, Complex.conj_im, neg_add]
  -- @@END@@

/-! ## 4.4 超越函数与三角

超越函数带来了一种新的"义务"：用引理时往往要**补前提**
（`Real.sq_sqrt` 要 `0 ≤ x`，`Real.log_mul` 要 `0 < x`）。
另一个常用技巧是**反用**引理：`rw [← Real.sqrt_mul h]` 把两个根式合成一个。
三角函数的性质则是 `rw` 与 `ring` 的交替（源文件 §2.5.5）。
-/

#check Real.sq_sqrt
#print Real.sq_sqrt
#check Real.sqrt_mul
#print Real.sqrt_mul
#check Real.sqrt_nonneg
#check Real.sin_sq_add_cos_sq
#check Real.cos_sub
#check Real.cos_add
#check Real.sin_periodic

-- [4.4.1] 前提债：每次 apply Real.sq_sqrt 之后，剩下要证的就是谁非负。
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x ^ 2 + Real.sqrt y ^ 2 = x + y := by
  -- @@SOLUTION@@
  have hx' : Real.sqrt x ^ 2 = x := by
    apply Real.sq_sqrt
    exact hx
  have hy' : Real.sqrt y ^ 2 = y := by
    apply Real.sq_sqrt
    exact hy
  rw [hx', hy']
  -- @@END@@

-- [4.4.2] 反用引理：把 √2 * √2 合成一个根号。
example : Real.sqrt 2 * Real.sqrt 2 = 2 := by
  -- @@SOLUTION@@
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  -- @@END@@

-- [4.4.3] 三角恒等式：有的库里有现成的，有的要 rw + ring。
example (θ : ℝ) : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
  -- @@SOLUTION@@
  exact Real.sin_sq_add_cos_sq θ
  -- @@END@@

example (α β : ℝ) : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := by
  -- @@SOLUTION@@
  exact Real.cos_sub α β
  -- @@END@@

-- [4.4.4] 积化和差：第一步把 cos(α - β)、cos(α + β) 展开，第二步 ring 收尾。
example (α β : ℝ) : Real.cos α * Real.cos β = (Real.cos (α - β) + Real.cos (α + β)) / 2 := by
  -- @@SOLUTION@@
  rw [Real.cos_sub, Real.cos_add]
  ring
  -- @@END@@

-- [4.4.5] 周期性。
example : Function.Periodic Real.sin (2 * Real.pi) := by
  -- @@SOLUTION@@
  exact Real.sin_periodic
  -- @@END@@

-- [4.4.6] 根号与绝对值（先自己找引理）。
example (x : ℝ) : Real.sqrt (x ^ 2) = |x| := by
  -- @@SOLUTION@@
  exact Real.sqrt_sq_eq_abs x
  -- @@END@@

-- [4.4.7] 倍角公式的一个变形：先用倍角公式展开，再用 sin² + cos² 消掉一项，最后 ring。
example (θ : ℝ) : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
  -- @@SOLUTION@@
  rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq θ]
  ring
  -- @@END@@

-- [4.4.8] 指数与对数互为逆运算（两条）。
example (x : ℝ) : Real.log (Real.exp x) = x := by
  -- @@SOLUTION@@
  exact Real.log_exp x
  -- @@END@@

example (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x) = x := by
  -- @@SOLUTION@@
  exact Real.exp_log hx
  -- @@END@@

-- [4.4.9] 二元均值不等式：先把根号乘开（反用 sqrt_mul），再让 nlinarith 用两个平方非负收尾。
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  -- @@SOLUTION@@
  rw [Real.sqrt_mul ha b]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]
  -- @@END@@

/-! ## 5. ℚ² 的向量运算与线性相关

`MyVect` 表示 ℚ²，向量写作 `![x, y]`，`u 0`、`u 1` 是它的两个坐标。
本节证明向量运算法则、线性相关性，以及线性组合的存在与唯一性。
-/

/-! ### 5.1 定义与坐标工具 -/

abbrev MyVect := Fin 2 → ℚ

namespace MyVect

def add (u v : MyVect) : MyVect := fun i => u i + v i
def smul (a : ℚ) (u : MyVect) : MyVect := fun i => a * u i
def zero : MyVect := ![0, 0]

-- +、•、0 沿用函数的逐坐标运算，分别就是上述运算。
-- 减法也逐坐标计算：(u - v) i = u i - v i。
theorem eq_iff (u v : MyVect) : u = v ↔ u 0 = v 0 ∧ u 1 = v 1 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · intro h
    funext i
    fin_cases i
    · exact h.1
    · exact h.2

@[simp] theorem add_coord (u v : MyVect) (i : Fin 2) : (u + v) i = u i + v i := by
  rfl

@[simp] theorem sub_coord (u v : MyVect) (i : Fin 2) : (u - v) i = u i - v i := by
  rfl

@[simp] theorem smul_coord (a : ℚ) (u : MyVect) (i : Fin 2) : (a • u) i = a * u i := by
  rfl

@[simp] theorem zero_coord (i : Fin 2) : (0 : MyVect) i = 0 := by
  rfl

-- [5.1.1] 坐标计算热身。
example : (2 : ℚ) • (![1, -1] : MyVect) + ![3, 4] = ![5, 2] := by
  -- @@SOLUTION@@
  rw [MyVect.eq_iff]
  constructor
  · norm_num
  · norm_num
  -- @@END@@

/-! ### 5.2 向量运算法则

证明下面三条运算法则。
`@[simp]` 把合适的化简规则登记给 simp；分配与合并的方向则用 rw 明确指定。
-/

-- [5.2.1] 合并同一个向量的系数。
theorem combine_smul (a b : ℚ) (u : MyVect) : a • u + b • u = (a + b) • u := by
  -- @@SOLUTION@@
  rw [MyVect.eq_iff]
  constructor
  · simp only [add_coord, smul_coord]
    ring
  · simp only [add_coord, smul_coord]
    ring
  -- @@END@@

-- [5.2.2] 数乘对向量加法的分配律。
theorem smul_add (a : ℚ) (u v : MyVect) : a • (u + v) = a • u + a • v := by
  -- @@SOLUTION@@
  rw [MyVect.eq_iff]
  constructor
  · simp only [smul_coord, add_coord]
    ring
  · simp only [smul_coord, add_coord]
    ring
  -- @@END@@

-- [5.2.3] 连续数乘可以合并。
@[simp] theorem smul_smul (a b : ℚ) (u : MyVect) : a • (b • u) = (a * b) • u := by
  -- @@SOLUTION@@
  rw [MyVect.eq_iff]
  constructor
  · simp only [smul_coord]
    ring
  · simp only [smul_coord]
    ring
  -- @@END@@

-- 以下是零向量、数乘和减法的常用引理。
-- funext i 把向量等式转成任意一个坐标上的等式。
@[simp] theorem zero_smul (u : MyVect) : (0 : ℚ) • u = 0 := by
  funext i
  simp

@[simp] theorem one_smul (u : MyVect) : (1 : ℚ) • u = u := by
  funext i
  simp

@[simp] theorem smul_zero (a : ℚ) : a • (0 : MyVect) = 0 := by
  funext i
  simp

@[simp] theorem add_zero (u : MyVect) : u + 0 = u := by
  funext i
  simp

@[simp] theorem zero_add (u : MyVect) : (0 : MyVect) + u = u := by
  funext i
  simp

@[simp] theorem sub_self (u : MyVect) : u - u = 0 := by
  funext i
  simp

theorem sub_smul (a b : ℚ) (u : MyVect) : (a - b) • u = a • u - b • u := by
  funext i
  simp only [smul_coord, sub_coord]
  ring

theorem add_add_add_comm (u v w z : MyVect) : (u + v) + (w + z) = (u + w) + (v + z) := by
  exact _root_.add_add_add_comm u v w z

-- 两个线性组合相减时，对应系数相减。
theorem linearCombination_sub (a b c d : ℚ) (u v : MyVect) :
    (a • u + b • v) - (c • u + d • v) = (a - c) • u + (b - d) • v := by
  rw [MyVect.sub_smul, MyVect.sub_smul, _root_.sub_add_sub_comm]

#check MyVect.combine_smul
#check MyVect.smul_add
#check MyVect.smul_smul
#check MyVect.linearCombination_sub

/-! ### 5.3 线性相关与线性无关

相关：存在不全为零的系数，使线性组合为零。
无关：线性组合为零时，系数只能全为零。
-/

def Dependent (u v : MyVect) : Prop :=
  ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧ a • u + b • v = 0

def Independent (u v : MyVect) : Prop :=
  ∀ a b : ℚ, a • u + b • v = 0 → a = 0 ∧ b = 0

-- [5.3.1] 一个向量与它的任意倍数线性相关。
theorem dependent_smul (u : MyVect) (c : ℚ) : Dependent u (c • u) := by
  -- @@SOLUTION@@
  use c, -1
  constructor
  · right
    norm_num
  · rw [MyVect.smul_smul, MyVect.combine_smul]
    have hcoeff : c + (-1) * c = 0 := by ring
    rw [hcoeff]
    simp
  -- @@END@@

-- (1, 2) 与 (3, 6) 线性相关。
example : Dependent (![1, 2] : MyVect) ((3 : ℚ) • ![1, 2]) := by
  exact dependent_smul ![1, 2] 3

-- [5.3.2] 证明 (1, 1)、(1, -1) 线性无关。
theorem diagonal_independent : Independent ![1, 1] ![1, -1] := by
  -- @@SOLUTION@@
  intro a b h
  rw [MyVect.eq_iff] at h
  rcases h with ⟨h₀, h₁⟩
  simp at h₀ h₁
  constructor
  · linarith
  · linarith
  -- @@END@@

/-! ### 5.4 线性组合的存在与唯一性 -/

def InSpan (u v w : MyVect) : Prop :=
  ∃ a b : ℚ, w = a • u + b • v

-- [5.4.1] 把任意向量 w 写成 (1, 1)、(1, -1) 的线性组合。
theorem diagonal_spans (w : MyVect) : InSpan ![1, 1] ![1, -1] w := by
  -- @@SOLUTION@@
  use (w 0 + w 1) / 2, (w 0 - w 1) / 2
  rw [MyVect.eq_iff]
  constructor
  · simp
    ring
  · simp
    ring
  -- @@END@@

-- [5.4.2] 线性无关向量的线性组合具有唯一的系数。
-- 提示：使用 linearCombination_sub 和 huv。
theorem Independent.unique_coeffs {u v : MyVect} (huv : Independent u v)
    {a b c d : ℚ} (h : a • u + b • v = c • u + d • v) : a = c ∧ b = d := by
  -- @@SOLUTION@@
  have hzero : (a - c) • u + (b - d) • v = 0 := by
    rw [← MyVect.linearCombination_sub, h]
    simp
  obtain ⟨hac, hbd⟩ := huv (a - c) (b - d) hzero
  constructor
  · exact sub_eq_zero.mp hac
  · exact sub_eq_zero.mp hbd
  -- @@END@@

-- 应用于 (1, 1)、(1, -1)。
example (a b c d : ℚ)
    (h : a • (![1, 1] : MyVect) + b • ![1, -1] =
      c • (![1, 1] : MyVect) + d • ![1, -1]) : a = c ∧ b = d := by
  exact diagonal_independent.unique_coeffs h

/-! ### 5.5 综合题：一组新的线性无关向量

若 u、v 无关，证明 u + v、u + 2 • v 也无关。
提示：将新的线性组合整理成 u、v 的线性组合，再应用原来的无关性。
-/

-- [5.5.1] 请使用 5.2 的引理。
theorem Independent.change_pair {u v : MyVect} (huv : Independent u v) :
    Independent (u + v) (u + (2 : ℚ) • v) := by
  -- @@SOLUTION@@
  intro a b h
  rw [MyVect.smul_add, MyVect.smul_add, MyVect.smul_smul,
    MyVect.add_add_add_comm, MyVect.combine_smul, MyVect.combine_smul] at h
  obtain ⟨h₁, h₂⟩ := huv (a + b) (a + b * 2) h
  constructor
  · linarith
  · linarith
  -- @@END@@

-- 取 u = (1, 1)、v = (1, -1)。
example : Independent
    ((![1, 1] : MyVect) + ![1, -1])
    ((![1, 1] : MyVect) + (2 : ℚ) • ![1, -1]) := by
  exact diagonal_independent.change_pair

end MyVect

/-!
## 速查表（按 tactic 查）

| 想做的事 | tactic |
| --- | --- |
| 改写目标或假设 | `rw [h]` / `rw [← h]` / `rw [h] at h₂` |
| 交出完整证明 | `exact ...` |
| 把目标拆成前提 | `apply ...` |
| 拆 ∧ 与 ↔ | `constructor` |
| 引入 → 的条件与 ∀ 的变量 | `intro ...` |
| 拆假设里的 ∧ ∨ ∃ | `rcases ... with ⟨...⟩` / `obtain ⟨...⟩` |
| 给出 ∃ 的见证 | `use ...` |
| 保存中间结论 / 起短名字 | `have h : ... := by ...` / `let t := ...` |
| 写推导链 | `calc ... = ... := by ...` |
| 分类讨论 | `by_cases h : P` |
| 计算型命题 | `rfl` / `decide` / `norm_num` |
| 展开一个定义 | `unfold 定义名` / `simp only [定义名]` |
| 多项式恒等式 | `ring` / `ring_nf` |
| 清分母 | `field_simp` |
| 多项式次数 | `compute_degree!` |
| 化简 | `simp` / `simp only [...]` |
| 线性算术 | `linarith` / `linarith [事实]` |
| ℤ/ℕ 与整除 | `omega` |
| 非线性不等式 | `nlinarith [sq_nonneg ...]` |
| 制造非负前提 | `positivity` |
| 命题逻辑 | `tauto` |
| 不知道用哪条定理 | `exact?` / `apply?` |
| 不知道 simp 用了什么 | `simp?` |
-/

end ElementaryAlgebra.Tactics
