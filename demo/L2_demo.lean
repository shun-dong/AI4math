import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace TypeConversion.LiveDemo

/-!
R：读 Lean；D：等式；B：数字定义；N：数值转换；T：tactic；S：集合；P：多项式。
注释中的错误行可在现场打开，观察后恢复。片段直接用于 Typst 投影片。
-/
-- R01:START
def twice (n : ℕ) : ℕ := n + n

#check twice     -- ℕ → ℕ
#eval twice 3    -- 6
#check (3 : ℚ)   -- 3 : ℚ
-- R01:END

-- R02:START
def add (a b : ℕ) : ℕ := a + b

#check add      -- ℕ → ℕ → ℕ
#check add 3    -- ℕ → ℕ
#eval add 3 4   -- 7

#eval (fun n : ℕ => n + 1) 4  -- 5
-- R02:END

-- R03:START
#check (2 + 3 = (5 : ℕ))  -- Prop

theorem two_add_three : (2 : ℕ) + 3 = 5 := rfl

example (n : ℕ) (h : n = 3) : n = 3 := h

example (n : ℕ) (h : n = 3) : n = 3 := by
  exact h
-- R03:END

-- R04:START
def firstExplicit (α : Type) (x _y : α) : α := x
def first {α : Type} (x _y : α) : α := x

#eval firstExplicit ℕ 3 4       -- 3
#eval first (3 : ℕ) 4          -- 3
#eval first (α := ℚ) 3 4       -- 3
#eval @first ℚ 3 4             -- 3
-- R04:END

-- R05:START
section
variable {α : Type} (x : α)

def keep : α := x
#check keep  -- keep {α : Type} (x : α) : α

end

#eval keep (3 : ℕ)  -- 3
-- R05:END

-- R06:START
def addTwo {α : Type} [Add α] (x y : α) : α :=
  x + y

#eval addTwo (3 : ℕ) 4     -- 7
#eval addTwo (3 : ℤ) (-4)  -- -1
-- R06:END

-- D01:START
example : twice 3 = 6 := rfl
example (n : ℕ) : twice n = n + n := rfl

example (n : ℕ) : n + 0 = n := rfl
-- D01:END

-- D02:START
-- example (n : ℕ) : 0 + n = n := rfl

example (n : ℕ) : 0 + n = n := Nat.zero_add n

example (n : ℕ) (h : n = 3) : n + 0 = 3 := h
-- D02:END

-- D03:START
example (n m : ℕ) (h : n = m) : n + 1 = m + 1 := by
  rw [h]

-- example (n m : ℕ) (h : n = m) : n = m := rfl
-- D03:END

-- N01:START
#check (3 : ℕ)
#check (3 : ℤ)
#check (3 : ℚ)
#check (3 : ℝ)
-- N01:END

-- B01:START
#print Nat
-- inductive Nat where
--   | zero : Nat
--   | succ : Nat → Nat

example : Nat.succ (Nat.succ Nat.zero) = 2 := rfl
example (n : ℕ) : Nat.succ n = n + 1 := rfl
#eval (0 : ℕ) ^ 0  -- 1
-- B01:END

-- B02:START
#print Int
-- ofNat   : ℕ → ℤ
-- negSucc : ℕ → ℤ

#eval Int.ofNat 3    -- 3
#eval Int.negSucc 2  -- -3

example (n : ℕ) : (n : ℤ) = Int.ofNat n := rfl
-- B02:END

-- B03:START
def q : ℚ := 6 / 8

#check q.num  -- ℤ
#check q.den  -- ℕ
#eval q.num  -- 3
#eval q.den  -- 4

example : q = 3 / 4 := by norm_num [q]
-- B03:END

-- B04:START
example : (1 : ℝ) / 3 + 2 / 3 = 1 := by
  norm_num

example (x : ℝ) (hx : x ≠ 0) : x / x = 1 := by
  exact div_self hx

example : (0 : ℝ) / 0 = 0 := by norm_num
-- B04:END

-- B05:START
def z : ℂ := ⟨1, 2⟩

example : z.re = 1 := rfl
example : z.im = 2 := rfl
example : z = 1 + 2 * Complex.I := by
  norm_num [z, Complex.ext_iff]

example (r : ℝ) : (r : ℂ).im = 0 := rfl
-- B05:END

-- N02:START
def toInteger (n : ℕ) : ℤ := n
def toRational (n : ℕ) : ℚ := (n : ℚ)
def toReal (q : ℚ) : ℝ := (q : ℝ)

example (n : ℕ) : n = (n : ℤ) := rfl
-- N02:END

-- N03:START
#eval ((2 - 3 : ℕ) : ℤ)  -- 0
#eval (2 : ℤ) - 3        -- -1

#eval ((7 / 2 : ℕ) : ℚ)  -- 3
#eval (7 : ℚ) / 2        -- 7/2

#eval Int.toNat (-3)     -- 0
-- N03:END

-- T01:START
example : ((2 - 3 : ℕ) : ℤ) = 0 := by
  norm_num

example : (2 : ℤ) - 3 = -1 := by
  norm_num

example : (7 : ℚ) / 2 + 1 / 2 = 4 := by
  norm_num
-- T01:END

-- T02:START
example (m n : ℕ) :
    ((m + n : ℕ) : ℤ) = (m : ℤ) + (n : ℤ) := by
  norm_cast

example (m n : ℕ) (h : (m : ℤ) = (n : ℤ)) :
    m + 1 = n + 1 := by
  norm_cast at h
  rw [h]
-- T02:END

-- T03:START
example (m n : ℕ) (h : m ≤ n) :
    (m : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast h

example (m n : ℕ) (h : (m : ℤ) < (n : ℤ)) : m < n := by
  exact_mod_cast h
-- T03:END

-- N04:START
def averageWrong (a b : ℕ) : ℚ := ((a + b) / 2 : ℕ)
def average (a b : ℕ) : ℚ := ((a : ℚ) + (b : ℚ)) / 2

#eval averageWrong 2 3  -- 2
#eval average 2 3       -- 5/2

example : average 2 3 = 5 / 2 := by
  norm_num [average]
-- N04:END

-- S01:START
example : Set ℕ = (ℕ → Prop) := rfl

def small : Set ℕ := {n | n < 5}
example : small = (fun n : ℕ => n < 5) := rfl
example (n : ℕ) : (n ∈ small) = (n < 5) := rfl

example : 3 ∈ small := by norm_num [small]
-- S01:END

-- S02:START
def allNats : Set ℕ := Set.univ
def noNats : Set ℕ := ∅
def chosen : Set ℕ := {1, 2, 3}

example : allNats = (fun _ => True) := rfl
example : noNats = (fun _ => False) := rfl
example (n : ℕ) :
    (n ∈ chosen) ↔ n = 1 ∨ n = 2 ∨ n = 3 := by
  simp [chosen]
-- S02:END

-- S03:START
example (s t : Set ℕ) (n : ℕ) :
    (n ∈ s ∩ t) ↔ (n ∈ s ∧ n ∈ t) := Iff.rfl

example (s t : Set ℕ) (n : ℕ) :
    (n ∈ s ∪ t) ↔ (n ∈ s ∨ n ∈ t) := Iff.rfl

example : 3 ∈ chosen ∩ small := by
  norm_num [chosen, small]
-- S03:END

noncomputable section
-- P01:START
open Polynomial

def p : ℤ[X] := X ^ 2 + C 2 * X + C 3

#check p           -- Polynomial ℤ
#check (X : ℤ[X])  -- 不定元
#check C (2 : ℤ)   -- 常数多项式

def linear (a b : ℤ) : ℤ[X] := C a * X + C b
-- P01:END

-- P02:START
#check p.coeff 1  -- ℤ
#check p.eval 2   -- ℤ

example : p.coeff 1 = 2 := by simp [p]
example : p.coeff 2 = 1 := by simp [p, coeff_X]
example : p.coeff 5 = 0 := by simp [p, coeff_X]

example : p.eval 2 = 11 := by norm_num [p]
-- P02:END

-- P03:START
example : p.natDegree = 2 := by
  unfold p
  compute_degree!

example : ((X + 1) ^ 2 : ℤ[X]) = X ^ 2 + 2 * X + 1 := by
  ring

example (x : ℚ) : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  ring
-- P03:END

-- P04:START
def pQ : ℚ[X] := p.map (algebraMap ℤ ℚ)

example : pQ = X ^ 2 + C 2 * X + C 3 := by
  simp [pQ, p, C_ofNat]

example : pQ.eval (1 / 2) = 17 / 4 := by
  norm_num [pQ, p]
-- P04:END

end
end TypeConversion.LiveDemo
