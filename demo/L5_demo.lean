import Mathlib

/-!
# AI4math seminar 5 — type-class demo
Liu Peixuan · Sustech math department
Target: the project's Lean and Mathlib v4.23.0-rc2 toolchain.

Part I introduces type classes. Part II contains all 52 group theory lecture
blocks in source order, with compatibility fixes for this project.
The original exercise placeholders (`sorry`) remain for students to complete.
-/
namespace AI4Math.Seminar5
universe u

/-! ## Introduction: a record stores operations and laws that refer to those operations. -/

-- BEGIN SLIDE SNIPPET dependent_record
structure OpData (A : Type u) where
  op : A → A → A
  assoc : ∀ x y z, op (op x y) z = op x (op y z)

def natOpData : OpData Nat where
  op := Nat.add
  assoc := Nat.add_assoc
-- END SLIDE SNIPPET dependent_record

/-! ## Introduction: the dependent-pair model. The two conversion functions expose the same package; this is not an assertion that the declarations are aliases. -/

-- BEGIN SLIDE SNIPPET sigma_record
structure PackedRecord where
  Carrier : Type
  data : OpData Carrier

abbrev PackedSigma := Σ A : Type, OpData A

def pack (p : PackedRecord) : PackedSigma :=
  ⟨p.Carrier, p.data⟩
def unpack (p : PackedSigma) : PackedRecord :=
  ⟨p.1, p.2⟩

example (p : PackedRecord) : unpack (pack p) = p := by
  cases p
  rfl
-- END SLIDE SNIPPET sigma_record

/-! ## Introduction: replace a record interface by a class interface; retain its dependent fields. -/

-- BEGIN SLIDE SNIPPET class_bridge
class Combine (A : Type u) where
  op : A → A → A
  assoc : ∀ x y z, op (op x y) z = op x (op y z)

def OpData.asCombine {A : Type u}
    (d : OpData A) : Combine A :=
  ⟨d.op, d.assoc⟩
-- END SLIDE SNIPPET class_bridge

/-! ## 1. Basic usage: define instances and request instance parameters. -/

-- BEGIN SLIDE SNIPPET class_decl
instance natCombine : Combine Nat where
  op := Nat.add
  assoc := Nat.add_assoc

def twice {A : Type u} [Combine A] (x : A) : A :=
  Combine.op x x

example : twice (4 : Nat) = 8 := rfl
-- END SLIDE SNIPPET class_decl

/-! ## 1. Basic usage: dictionary parameters are ordinary terms after elaboration. -/

-- BEGIN SLIDE SNIPPET explicit_dictionary
def usingExplicit {A : Type u}
    (d : Combine A) (x y : A) : A :=
  @Combine.op A d x y

example {A : Type u} [d : Combine A] (x : A) :
    twice x = @Combine.op A d x x := rfl

example : twice (4 : Nat) = @twice Nat natCombine 4 :=
  rfl
-- END SLIDE SNIPPET explicit_dictionary

/-! ## 1. Basic usage: make a dictionary stored in a package available to synthesis. -/

-- BEGIN SLIDE SNIPPET packed_instance
abbrev PackedCombine := Σ A : Type, Combine A

def twicePacked (p : PackedCombine) (x : p.1) : p.1 := by
  letI : Combine p.1 := p.2
  exact twice x

example (p : PackedCombine) (x : p.1) :
    twicePacked p x = @twice p.1 p.2 x := rfl
-- END SLIDE SNIPPET packed_instance

/-! ## 1. Basic usage: generic instances generate further instance goals. -/

-- BEGIN SLIDE SNIPPET recursive_instance
class Describe (A : Type u) where
  describe : A → String

instance : Describe Nat := ⟨toString⟩
instance {A : Type u} [Describe A] : Describe (List A) where
  describe xs :=
    "[" ++ String.intercalate ", " (xs.map Describe.describe) ++ "]"

#synth Describe (List Nat)
#eval Describe.describe ([1, 2, 3] : List Nat)
-- END SLIDE SNIPPET recursive_instance

/-! ## 1. Basic usage: namespace resolution and instance synthesis are separate. -/

-- BEGIN SLIDE SNIPPET namespace_usage
namespace Ops
instance boolCombine : Combine Bool where
  op x y := x && y
  assoc := by decide
open Combine in
def duplicate {A : Type u} [Combine A] (x : A) : A :=
  op x x
end Ops
example : Ops.duplicate true = true := rfl
-- END SLIDE SNIPPET namespace_usage

/-! ## 1. Basic usage: section parameters and include. A namespace adds a name prefix; a section does not. -/

-- BEGIN SLIDE SNIPPET section_usage
section
variable {A : Type u} [Combine A]
def sectionTwice (x : A) : A := Combine.op x x
end
section
variable {P : Prop} (h : P)
include h in
theorem useSectionFact : P := h
end
#print sectionTwice
#print useSectionFact
-- END SLIDE SNIPPET section_usage

/-! ## 1. Composition: keep an existing group dictionary as a field. The subgroup field depends on this exact dictionary. -/

-- BEGIN SLIDE SNIPPET group_composition
structure GroupWithSubgroup (G : Type u) where
  group : Group G
  subgroup : @Subgroup G group

def invertChosen {G : Type u}
    (s : GroupWithSubgroup G) (x : G) : G := by
  letI : Group G := s.group
  exact x⁻¹
-- END SLIDE SNIPPET group_composition

/-! ## 1. Inheritance: Group directly extends DivInvMonoid in this Mathlib version. -/

-- BEGIN SLIDE SNIPPET group_parents
def forgetGroup {G : Type u}
    (s : Group G) : DivInvMonoid G :=
  s.toDivInvMonoid

example {G : Type u} [Group G] : Monoid G :=
  inferInstance

-- This theorem needs only the parent interface.
example {G : Type u} [DivInvMonoid G] (a b : G) :
    a / b = a * b⁻¹ := div_eq_mul_inv a b
-- END SLIDE SNIPPET group_parents

/-! ## 1. Inheritance: a child class adds a chosen point and supplies the parent Group interface. -/

-- BEGIN SLIDE SNIPPET marked_group
class MarkedGroup (G : Type u) extends Group G where
  mark : G

def inverseMark {G : Type u} [MarkedGroup G] : G :=
  (MarkedGroup.mark : G)⁻¹

example {G : Type u} [MarkedGroup G] : Group G :=
  inferInstance
-- END SLIDE SNIPPET marked_group

/-! ## 1. Multiple inheritance: actual CommGroup extends Group and CommMonoid. The new commutativity law refers to the existing multiplication. -/

-- BEGIN SLIDE SNIPPET commgroup_upgrade
def upgradeToCommGroup {G : Type u} [Group G]
    (h : ∀ a b : G, a * b = b * a) : CommGroup G where
  mul_comm := h

example {G : Type u} [CommGroup G] : CommMonoid G :=
  inferInstance
-- END SLIDE SNIPPET commgroup_upgrade

/-! ## 1. Derived instances: DivisionMonoid and CancelMonoid are obtained by proving additional laws, not by additional direct extends clauses on Group. -/

-- BEGIN SLIDE SNIPPET derived_instances
#check Group.toDivInvMonoid   -- generated parent projection
#check Group.toDivisionMonoid -- separately proved instance
#check Group.toCancelMonoid   -- separately proved instance

example {G : Type u} [Group G] : DivisionMonoid G :=
  inferInstance
example {G : Type u} [Group G] : CancelMonoid G :=
  inferInstance
-- END SLIDE SNIPPET derived_instances

/-! ## 1. Defaults: this separate carrier uses integer addition as its group multiplication. The inherited division and power fields use their defaults. This is supplementary, not a replacement for any lecture exercise. -/

-- BEGIN SLIDE SNIPPET custom_group
@[ext] structure IntAsGroup where
  val : ℤ

instance : Group IntAsGroup where
  mul a b := ⟨a.val + b.val⟩
  one := ⟨0⟩
  inv a := ⟨-a.val⟩
  mul_assoc a b c := by
    apply IntAsGroup.ext
    exact add_assoc a.val b.val c.val
  one_mul a := by
    apply IntAsGroup.ext
    exact zero_add a.val
  mul_one a := by
    apply IntAsGroup.ext
    exact add_zero a.val
  inv_mul_cancel a := by
    apply IntAsGroup.ext
    exact neg_add_cancel a.val

example (a b : IntAsGroup) : a / b = a * b⁻¹ := rfl
#eval (((⟨7⟩ : IntAsGroup) / ⟨2⟩).val) -- 5
-- END SLIDE SNIPPET custom_group

/-! ## 2. Type conversions: a value-to-value conversion. -/

-- BEGIN SLIDE SNIPPET coe_value
structure UserId where
  value : Nat

instance : Coe UserId Nat where
  coe x := x.value

def fortyTwo : UserId := ⟨42⟩
example : (↑fortyTwo : Nat) = 42 := rfl
-- END SLIDE SNIPPET coe_value

/-! ## 2. Type conversions: a bundled object used as a function. -/

-- BEGIN SLIDE SNIPPET coe_function
structure Endomap (A : Type) where
  run : A → A

instance {A : Type} : CoeFun (Endomap A)
    (fun _ => A → A) where
  coe f := f.run

def increment : Endomap Nat := ⟨fun n => n + 1⟩
example : increment 4 = 5 := rfl
-- END SLIDE SNIPPET coe_function

/-! ## 2. Type conversions: a bundled object used to specify a type. -/

-- BEGIN SLIDE SNIPPET coe_sort
structure TypeBox where
  carrier : Type

instance : CoeSort TypeBox Type where
  coe b := b.carrier

def naturals : TypeBox := ⟨Nat⟩
example : naturals := (3 : Nat)
-- END SLIDE SNIPPET coe_sort

/-! ## 2. Type conversions: H : Subgroup G is a value; x : H uses the associated subtype via CoeSort. -/

-- BEGIN SLIDE SNIPPET subgroup_as_type
example {G : Type u} [Group G] (H : Subgroup G) :
    (↥H) = {g : G // g ∈ H} := rfl

example {G : Type u} [Group G] (H : Subgroup G)
    (g : G) (hg : g ∈ H) : H := ⟨g, hg⟩

example {G : Type u} [Group G]
    (H : Subgroup G) (x : H) : (↑x : G) ∈ H :=
  x.property
-- END SLIDE SNIPPET subgroup_as_type

/-! ## 2. Type conversions: a homomorphism has a callable function view; a subgroup has an element type with inherited operations. -/

-- BEGIN SLIDE SNIPPET hom_coercion
example {G H : Type u} [Group G] [Group H]
    (f : G →* H) (x y : G) :
    f (x * y) = f x * f y := f.map_mul x y

example {G : Type u} [Group G] (H : Subgroup G) :
    Group H := inferInstance
-- END SLIDE SNIPPET hom_coercion

/-! ## 3. Design habits: a temporary hypothesis versus a guarantee that travels with the object. -/

-- BEGIN SLIDE SNIPPET even_bundle
abbrev EvenNumber := {n : Nat // Even n}

example (a b : Nat) (ha : Even a) (hb : Even b) :
    Even (a + b) := ha.add hb

def addEven (a b : EvenNumber) : EvenNumber :=
  ⟨a.val + b.val, a.property.add b.property⟩

example (a b : EvenNumber) :
    (addEven a b).val = a.val + b.val := rfl
-- END SLIDE SNIPPET even_bundle

/-! ## 3. Design habits: lift an operation using closure; prove subtype equality using the underlying values. -/

-- BEGIN SLIDE SNIPPET subtype_equality
def liftBinary {A : Type u} {P : A → Prop}
    (op : A → A → A)
    (closed : ∀ {a b}, P a → P b → P (op a b))
    (a b : {x : A // P x}) : {x : A // P x} :=
  ⟨op a.val b.val, closed a.property b.property⟩

example (a b : EvenNumber) (h : a.val = b.val) : a = b :=
  Subtype.ext h
-- END SLIDE SNIPPET subtype_equality

/-! ## 3. Design habits: ambient structure, selected subobject, and an extra background property. -/

-- BEGIN SLIDE SNIPPET design_subgroups
example {G : Type u} [Group G]
    (H : Subgroup G) (x y : H) :
    (↑(x * y) : G) ∈ H := (x * y).property

example {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal] : Group (G ⧸ H) :=
  inferInstance
-- END SLIDE SNIPPET design_subgroups

/-! ## 3. Design habits: types can record compatibility information; dependent pairs return an index with matching data. -/

-- BEGIN SLIDE SNIPPET indexed
abbrev SizedList (A : Type u) (n : Nat) :=
  {xs : List A // xs.length = n}

def packList {A : Type u} (xs : List A) :
    Σ n : Nat, SizedList A n :=
  ⟨xs.length, ⟨xs, rfl⟩⟩

def transport {A : Type u} {m n : Nat}
    (h : m = n) (xs : SizedList A m) : SizedList A n :=
  h ▸ xs
-- END SLIDE SNIPPET indexed

end AI4Math.Seminar5


-- ============================================================
-- PART II: THE COMPLETE ORIGINAL GROUP THEORY LECTURE
-- ============================================================

-- PART II: COMPLETE GROUP THEORY LECTURE — COMPATIBLE DEMO.
-- All 52 lecture blocks follow in their original order, with prose as comments.
-- Proofs and declarations are adjusted for this project's Mathlib version.
-- Unfinished structure templates are examples, not global instances: their
-- admitted laws must not affect type-class synthesis in later proofs.
-- Exercises retain their original sorry placeholders; some exercise statements
-- are false or underspecified and require additional hypotheses before proving.
open Equiv Equiv.Perm DihedralGroup Polynomial
universe u u1 u2 u_1
namespace OriginalLecture

-- # 3. Group Theory
-- 
-- ## 3.1 Group Basic
-- 
-- In standard mathematical textbooks, the groups we typically refer to are algebraic structures consisting of a set S equipped with a binary operation *. This operation must satisfy three fundamental axioms:
-- 1. **Associativity**: $ \quad \forall a, b, c \in S, (a \ast b) \ast c = a \ast (b \ast c) $
-- 2. **Identity element**: $ \exists e \in S,\, \text{ such that } \forall a \in S,\, e \cdot a = a \cdot e = a $
-- 3. **Inverse element**: $ \forall a \in S,\,    \exists a^{-1} \in S \text{ such that } a \cdot a^{-1} = a^{-1} \cdot a = e $
-- 
-- In Lean4, we define groups in a similar manner, however, in Mathlib, the axioms that need to be verified may differ slightly.
-- 

-- BEGIN ORIGINAL BLOCK 001; source line 13
/- Ex0. How to define a Group in Lean 4 -/
example (R : Type u) : Group (Set R) where
  -- Define the group multiplication operation
  mul := by
    sorry
  -- Prove associativity: ∀ (a b c : Set R), a * b * c = a * (b * c)
  mul_assoc := by
    sorry
  -- The identity element in Group R
  one := by
    sorry
  -- One is a left neutral element for multiplication
  one_mul := by
    sorry
  -- One is a right neutral element for multiplication
  mul_one := by
    sorry
  -- Invert an element of α, denoted by a⁻¹
  inv := by
    sorry
  -- Inverse property: ∀ (a : Set R), a⁻¹ * a = 1
  inv_mul_cancel := by
    sorry
-- END ORIGINAL BLOCK 001

-- 
-- You need to verify one by one whether the defined set and operation satisfy all the properties mentioned above. The next subsection will provide some examples of existing groups in Mathlib.
-- 
-- ### 3.1.1 The Definition of Group
-- 
-- Some familiar examples of groups include the multiplicative group of real numbers ℝˣ = {r : ℝ | r ≠ 0} and the multiplicative group of rational numbers ℚˣ = {q : ℚ | q ≠ 0}. Fortunately, Mathlib already provides definitions for these examples.
-- 

-- BEGIN ORIGINAL BLOCK 002; source line 45
-- ℚˣ = {q : ℚ | q ≠ 0} is the multiplicative group of invertible rational numbers
example : Group ℚˣ := by infer_instance

-- ℝˣ = {r : ℝ | r ≠ 0} is the multiplicative group of invertible real numbers
example : Group ℝˣ := by infer_instance
-- END ORIGINAL BLOCK 002

-- 
-- 
-- Mathlib also provides an alternative way to define groups - using addition instead of the default multiplication. The approach to verifying additive groups largely follows the same logic as for multiplicative groups.
-- 
-- 

-- BEGIN ORIGINAL BLOCK 003; source line 57
/--Ex1. How to define an AddGroup in Lean 4-/
example (R : Type u) : AddGroup (Set R) where
  -- Define the group addition operation
  add := by
    sorry

  -- Prove associativity: ∀ (a b c : Set R), a + b + c = a + (b + c)
  add_assoc := by
    sorry

  -- The zero element (additive identity) in the group
  zero := by
    sorry

  -- Zero is a left neutral element for addition
  zero_add := by
    sorry

  -- Zero is a right neutral element for addition
  add_zero := by
    sorry

  -- Definition of natural number scalar multiplication (n • a)
  nsmul := by
    sorry

  -- Property: 0 • a = 0
  nsmul_zero := by
    sorry

  -- Property: (n + 1) • a = a + n • a
  nsmul_succ := by
    sorry

  -- Definition of integer scalar multiplication (z • a)
  zsmul := by
    sorry

  -- Property: 0 • a = 0 (for integers)
  zsmul_zero' := by
    sorry

  -- Property: (n + 1) • a = a + n • a (for positive integers)
  zsmul_succ' := by
    sorry

  -- Property: -n • a = -(n • a) (for negative integers)
  zsmul_neg' := by
    sorry

  -- The additive inverse operation (unary negation)
  neg := by
    sorry

  -- Inverse property: ∀ (a : Set R), -a + a = 0
  neg_add_cancel := by
    sorry
-- END ORIGINAL BLOCK 003

-- 
-- We conclude this section with several examples of additive groups and verification of their properties.
-- 

-- BEGIN ORIGINAL BLOCK 004; source line 119
-- The integers ℤ form an additive group
example : AddGroup ℤ := by infer_instance

-- The rational numbers ℚ form an additive group
example : AddGroup ℚ := by infer_instance

-- The real numbers ℝ form an additive group
example : AddGroup ℝ := by infer_instance

-- Verification of group axioms for ℝ:

-- Associativity law: (a + b) + c = a + (b + c)
example (a b c : ℝ) : a + b + c = a + (b + c) := add_assoc a b c

-- Identity element: 0 + a = a
example (a : ℝ) : 0 + a = a := zero_add a

-- Inverse element: -a + a = 0
example (a : ℝ) : -a + a = 0 := neg_add_cancel a
-- END ORIGINAL BLOCK 004

-- 
-- 
-- ### 3.1.2 Examples of how to verify it is a group
-- 
-- In this section, we demonstrate two practical problems verifying that given sets with binary operations form groups. The specific Lean4 code implementation is provided below.
-- 
-- 
-- #### EX2.
-- 
-- Consider the set $\mathbb{R} \backslash\{-1\}$ of all real numbers except -1 . Define the operation $*$ by $$ a * b=a+b+a b . $$ Prove that this is a group.
-- 

-- BEGIN ORIGINAL BLOCK 005; source line 151
/-- EX2. Define a custom group structure on ℝ\{-1} with operation a*b = ab + a + b -/
def Group_EX_2 : Set ℝ := {x | x + 1 ≠ 0}

/-- Instance declaration for our custom group -/
noncomputable instance : Group (Group_EX_2) where
  -- Define the group multiplication operation
  mul := by
    dsimp [Group_EX_2]
    intro ⟨x, hx⟩ ⟨y, hy⟩
    use (x * y + x + y)
    dsimp [Group_EX_2]
    -- Key identity: xy + x + y + 1 = (x+1)(y+1)
    have : x*y + x + y + 1 = (x+1)*(y+1) := by ring
    rw [this]
    -- Non-zero product since x+1 ≠ 0 and y+1 ≠ 0
    exact mul_ne_zero hx hy

  -- Prove associativity: (a*b)*c = a*(b*c)
  mul_assoc := by
    intro ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩
    apply Subtype.val_inj.mp
    show (a * b + a + b)*c + (a * b + a + b) + c = a*(b*c + b + c) + a + (b*c + b + c)
    ring  -- Automatic proof via ring normalization

  -- The identity element is 0
  one := by
    use 0
    dsimp [Group_EX_2]
    simp  -- 0 + 1 ≠ 0 is trivial

  -- Left identity: 0*a = a
  one_mul := by
    intro ⟨a, ha⟩
    apply Subtype.val_inj.mp
    show 0*a + 0 + a = a
    ring  -- Simplifies to a = a

  -- Right identity: a*0 = a
  mul_one := by
    intro ⟨a, ha⟩
    apply Subtype.val_inj.mp
    show a*0 + a + 0 = a
    ring  -- Simplifies to a = a

  -- The inverse is a⁻¹ = 1/(a+1) - 1
  inv := by
    intro ⟨a, ha⟩
    use 1/(a+1) - 1
    dsimp [Group_EX_2]
    have : 1/(a+1) - 1 + 1 = 1/(a+1) := by simp
    rw [this]
    -- 1/(a+1) ≠ 0 since a+1 ≠ 0
    exact one_div_ne_zero ha

  -- Inverse property: a⁻¹ * a = 1
  inv_mul_cancel := by
    intro ⟨a, ha⟩
    apply Subtype.val_inj.mp
    show (1/(a+1) - 1)*a + (1/(a+1) - 1) + a = 0
    have : (a+1)/(a+1) = 1 := by
      exact (div_eq_one_iff_eq ha).mpr rfl
    calc
      _ = a/(a+1) - a + 1/(a+1) - 1 + a := by ring
      _ = a/(a+1) + 1/(a+1) - 1         := by ring
      _ = (a+1)/(a+1) - 1               := by ring
      _ = 1 - 1                          := by rw [this]
      _ = 0                              := by ring
-- END ORIGINAL BLOCK 005

-- 
-- 
-- 
-- #### EX3. Let $n$ be a positive integer; consider the set $$ G_{n}=\{1,-1\} \times \mathbb{Z}/n\mathbb{Z} . $$ We define an operation on this set by $$ (i,[k]) *(j,[m])=(i j,[m+j k]) . $$ Prove that this makes $G_{n}$ a group. Note: Do not neglect to show that this operation is associative!
-- 

-- BEGIN ORIGINAL BLOCK 006; source line 225
section ProductGroup
variable (n : ℕ)

/-- Define the product type as {1,-1} × ZMod n -/
abbrev Group_EX_3 := ({1, -1} : Finset ℤ) × (ZMod n)

-- Group instance for the product structure
instance : Group (Group_EX_3 n) where
  -- Define the group multiplication operation
  mul := fun (i, k) (j, m) =>
    (by
      -- First component: simple multiplication in {1,-1}
      use i * j
      fin_cases i <;> fin_cases j <;> simp,
    -- Second component: twisted addition that depends on the first component
    m + j * k)

  -- Proof of associativity
  mul_assoc := by
    intro a b c
    ext
    · -- Associativity for first component (regular multiplication)
      show a.1.1 * b.1.1 * c.1.1 = a.1.1 * (b.1.1 * c.1.1)
      exact Int.mul_assoc ↑a.1 ↑b.1 ↑c.1
    · -- Associativity for second component (twisted addition)
      dsimp [(· * ·)]
      show c.2 + c.1.1 * (b.2 + b.1.1 * a.2) = c.2 + c.1.1 * b.2 + (b.1.1 * c.1.1 : ℤ) * a.2
      simp only [Int.reduceNeg, Int.cast_mul]
      ring

  -- The identity element is (1, 0)
  one := by
    constructor
    · -- First component is 1 ∈ {1,-1}
      use 1
      exact Finset.mem_insert_self 1 {-1}
    · -- Second component is 0 ∈ ZMod n
      use 0

  -- Proof that identity is left identity
  one_mul := by
    intro a
    ext
    · -- First component: 1 * a = a
      show 1 * a.1.1 = a.1.1
      exact Int.one_mul ↑a.1
    · -- Second component: 0 + 1*a = a
      show a.2 + a.1.1 * 0 = a.2
      have: a.1.1 * 0 = 0 := by exact Int.mul_zero ↑a.1
      simp only [Int.reduceNeg, mul_zero, add_zero]

  -- Proof that identity is right identity
  mul_one := by
    intro a
    ext
    · -- First component: a * 1 = a
      show a.1.1 * 1 = a.1.1
      exact Int.mul_one ↑a.1
    · -- Second component: 0 + 1*a = a
      show 0 + (1 : ℤ) * a.2 = a.2
      simp only [Int.cast_one, Int.reduceNeg, one_mul, zero_add]

  -- Define the inverse operation
  inv := by
    intro a
    constructor
    · -- First component inverse is itself (since 1 and -1 are self-inverse)
      use a.1.1
      have := a.1.2
      exact this
    · -- Second component inverse is -a.2*a.1.1 (twisted by first component)
      use -a.2*a.1.1

  -- Proof of inverse property
  inv_mul_cancel := by
    intro a
    ext
    · -- First component: a * a⁻¹ = 1
      show a.1.1 * a.1.1 = 1
      -- Case analysis on whether a.1 is 1 or -1
      rcases List.mem_pair.mp a.1.2 with h | h
      · rw [h, mul_one]
      · rw [h]
        norm_num
    · -- Second component: a + a⁻¹*a = 0
      show a.2 + a.1.1 * (-a.2*a.1.1) = 0
      -- Both cases reduce via ring arithmetic
      rcases List.mem_pair.mp a.1.2 with h | h
      · rw [h]
        ring
      · rw [h]
        ring
end ProductGroup
-- END ORIGINAL BLOCK 006

-- 
-- 
-- ### 3.1.3 Order
-- 
-- The **order of a group** is the cardinality of its underlying set, denoted |G| for a group G. For finite groups, this is simply the number of elements in G, while infinite groups have order equal to their cardinality (e.g., ℵ₀ for countably infinite groups). Key properties include:
-- 
-- 1. **Lagrange's Theorem**: If H is a subgroup of finite group G, then |H| divides |G|. The formal statement of this theorem is shown below:
-- 

-- BEGIN ORIGINAL BLOCK 007; source line 326
/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive /-- **Lagrange's Theorem**: The order of an additive subgroup divides the order of its
ambient additive group. -/]

theorem card_subgroup_dvd_card {α : Type*} [Group α]
    (s : Subgroup α) : Nat.card s ∣ Nat.card α := by
  classical simp [Subgroup.card_eq_card_quotient_mul_card_subgroup s, @dvd_mul_left ℕ]
-- END ORIGINAL BLOCK 007

-- 
-- 2. **Order of elements**: The order of an element g ∈ G is the smallest positive integer n such that gⁿ = e (or infinite if no such n exists)
-- 

-- BEGIN ORIGINAL BLOCK 008; source line 337
-- Keep the demonstration definition separate from Mathlib's orderOf.
namespace OrderDefinition
/-- `orderOf x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `orderOf x` is `0` by convention. -/
@[to_additive
  /-- `addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it
  exists. Otherwise, i.e. if `a` is of infinite order, then `addOrderOf a` is `0` by convention. -/]

noncomputable def orderOf {G : Type*} [Monoid G] (x : G) : ℕ :=
  Function.minimalPeriod (x * ·) 1
end OrderDefinition
-- END ORIGINAL BLOCK 008

-- 
-- The order is fundamental in classifying groups and analyzing their structure, particularly in finite group theory and applications to symmetry and cryptography.
-- 
-- 
-- #### EX4. In an arbitrary group, let $a$ have finite order $n$, and let $k$ be a positive integer. If $(n, k)$ is the greatest common divisor of $n$ and $k$, and $[n, k]$ the least common multiple, show that the order of $a^{k}$ is $n /(n, k)=[n, k] / k$.
-- 

-- BEGIN ORIGINAL BLOCK 009; source line 353
/-- EX4. In an arbitrary group, let $a$ have finite order $n$, and let $k$ be a positive integer. If $(n, k)$ is the greatest common divisor of $n$ and $k$, and $[n, k]$ the least common multiple, show that the order of $a^{k}$ is $n /(n, k)=[n, k] / k$. -/
theorem Group_EX_4 {G : Type*} [Group G] (a : G) (n k : ℕ) (h : 0 < n) (h0 : 0 < k) (h1 : orderOf a = n) : orderOf (a ^ k) = n / (Nat.gcd n k) ∧ n / (Nat.gcd n k) = (Nat.lcm n k) / k := by
  constructor
  --Firstly, we separate the question into two parts.
  · have h2: 0 < n / (Nat.gcd n k) := by
      exact Nat.div_gcd_pos_of_pos_left k h
    --For the first part, We can easily get 0 < n / (Nat.gcd n k) by definition.
    apply (orderOf_eq_iff h2).mpr
    constructor
    --Then, we can apply the definition of order and simplify the task. After that, we divide it into two halves.
    · have h3 : n * (k / n.gcd k) = k * (n / n.gcd k) := by
        let t1 : (n.gcd k) ∣ k := by
          exact Nat.gcd_dvd_right n k
        let t2 : (n.gcd k) ∣ n := by apply Nat.gcd_dvd_left
        --For the first half, We can first easily get that (n.gcd k) ∣ k and (n.gcd k) ∣ n.
        qify [t1, t2]
        have : ((n.gcd k): ℚ) ≠ 0 := by
          dsimp
          refine Nat.cast_ne_zero.mpr ?_
          refine Nat.gcd_ne_zero_left ?_
          exact Nat.ne_zero_of_lt h
        field_simp [this]
        exact mul_comm _ _
      --Therefore, it is obvious that n * (k / n.gcd k) = k * (n / n.gcd k).
      have h4 : (a ^ n) = 1 := by
        refine orderOf_dvd_iff_pow_eq_one.mp ?_
        rw [h1]
      --Besides, by the definition of order, we can get that (a ^ n) = 1.
      calc
        _ = (a ^ n) ^ (k / n.gcd k) := by rw [← pow_mul, ← h3, ← pow_mul]
        _ = 1 ^ (k / n.gcd k) := by rw [h4]
        _ = 1 := by exact one_pow (k / n.gcd k)
      --After that, through some simple calculations and using the two lemmas proved above, we can easily get that (a ^ k) ^ (n / n.gcd k) = 1.
    · intro m h3 h4
      by_contra h5
      rw [← pow_mul] at h5
      --For the second half, We use the tactic by_contra to prove it.
      have h6 : orderOf a ∣ (k * m) := by
        exact orderOf_dvd_of_pow_eq_one h5
      rw [h1] at h6
      --According to the simple theorem about order, we can get that n ∣ k * m.
      have h7 : n ∣ n.gcd k * m := by
        exact Nat.dvd_gcd_mul_iff_dvd_mul.mpr h6
      --Then, by using the facts about gcd, we can have n ∣ n.gcd k * m.
      have h8 : n / n.gcd k ∣ m := by
        refine (Nat.div_dvd_iff_dvd_mul ?h ?hb).mpr ?_
        · exact Nat.gcd_dvd_left n k
        · exact Nat.gcd_pos_of_pos_left k h
        · exact h7
      --We divide the gcd of n and k on both sides, and we can get that n / n.gcd k ∣ m.
      have h9 : n / n.gcd k ≤ m := by
        exact Nat.le_of_dvd h4 h8
      --By using the definition of division, we can get n / n.gcd k ≤ m.
      have h10 : m < m := by
        exact Nat.lt_of_lt_of_le h3 h9
      exact (lt_self_iff_false m).mp h10
      --However, it is contrast to the definition of m. This finishes this part of proof.
  · have h2 : n * k = (Nat.gcd n k) * (Nat.lcm n k) := by
      exact Eq.symm (Nat.gcd_mul_lcm n k)
    --For the second part, by using the theory about gcd and lcm, we can get that n * k = (Nat.gcd n k) * (Nat.lcm n k).
    calc
      _ = n * k / (n.gcd k * k) := by
        refine Eq.symm (Nat.mul_div_mul_right n (n.gcd k) ?H)
        exact h0
      _ = (Nat.gcd n k) * (Nat.lcm n k) / (n.gcd k * k) := by rw [h2]
      _ = (Nat.lcm n k) / k := by
        apply Nat.mul_div_mul_left
        exact Nat.gcd_pos_of_pos_right n h0
    --After that, by dividing k and (Nat.gcd n k) on both sides, we can get n / (Nat.gcd n k) = (Nat.lcm n k) / k.
  --This finishes the whole proof.
-- END ORIGINAL BLOCK 009

-- 
-- 
-- #### EX5. If $G$ is an abelian group and if $G$ has an element of order $m$ and one of order $n$, where $m$ and $n$ are relatively prime, prove that $G$ has an element of order $m n$.
-- 

-- BEGIN ORIGINAL BLOCK 010; source line 430
/-- Ex5. If $G$ is an abelian group and if $G$ has an element of order $m$ and one of order $n$, where $m$ and $n$ are relatively prime, prove that $G$ has an element of order $m n$. -/
theorem Group_Basic_Ex_5 {G : Type*} [CommGroup G] (a b : G) (m n : ℕ) (cp : Nat.Coprime m n) (oa : orderOf a = m) (ob : orderOf b = n) : ∃ g : G, orderOf g = m * n := by
  use a * b
  -- We try to prove that a * b is the element we want.
  have h : (a * b) ^ (m * n) = 1 := by
    rw [mul_pow, ← oa, ← ob, pow_mul, pow_mul', pow_orderOf_eq_one, pow_orderOf_eq_one]
    simp
  -- We prove that a * b has order mn.
  -- We need to prove that (a * b) ^ (m * n) = 1 implies that the order of a * b divides m * n.
  have div1 : orderOf (a * b) ∣ (m * n)  := by exact orderOf_dvd_of_pow_eq_one h
  have oeq : (a * b) ^ orderOf (a * b) = 1 := by exact pow_orderOf_eq_one (a * b)
  -- We need to prove that m ∣ orderOf (a * b) and n ∣ orderOf (a * b), so that m * n ∣ orderOf (a * b) with the property that m and n are relatively prime.
  -- We know b ^ (orderOf (a * b) * m) = 1 since (a * b) ^ (orderOf (a * b) * m) = 1 and a ^ m = 1.
  have div2 : (m * n) ∣ orderOf (a * b) := by
    have h1 : b ^ (orderOf (a * b) * m) = 1 := by
      have oeq' : (a * b) ^ (orderOf (a * b) * m) = 1 := by rw [pow_mul, oeq, one_pow]
      rw [mul_pow, pow_mul', ← oa, pow_orderOf_eq_one, one_pow, one_mul, oa] at oeq'
      exact oeq'
    -- So, we prove that n ∣ orderOf (a * b).
    have h1' : n ∣ (orderOf (a * b) * m) := by rw[← ob];exact orderOf_dvd_of_pow_eq_one h1
    have h₁ : n ∣ orderOf (a * b) := by
      apply (Nat.Coprime.dvd_mul_right cp.symm).1
      exact h1'
  -- The same is for m ∣ orderOf (a * b).
    have h2 : a ^ (orderOf (a * b) * n) = 1 := by
      have oeq' : (a * b) ^ (orderOf (a * b) * n) = 1 := by rw [pow_mul, oeq, one_pow]
      rw [mul_pow, pow_mul, pow_mul', ← ob, pow_orderOf_eq_one, one_pow, mul_one, ob, ← pow_mul] at oeq'
      exact oeq'
    have h2' : m ∣ (orderOf (a * b) * n) := by rw[← oa];exact orderOf_dvd_of_pow_eq_one h2
    have h₂ : m ∣ orderOf (a * b) := by
      apply (Nat.Coprime.dvd_mul_right cp).1
      exact h2'
  -- Then using the coprime of m and n, we induce that lcm m n = m * n ∣ orderOf (a * b).
    have h₃ : Nat.lcm m n ∣ orderOf (a * b) := by
      exact Nat.lcm_dvd h₂ h₁
    have eq : m.lcm n = m * n := by apply Nat.Coprime.lcm_eq_mul cp
    exact eq ▸ h₃
  -- Finally, conclude that the order of a * b is m * n.
  exact Nat.dvd_antisymm div1 div2
-- END ORIGINAL BLOCK 010

-- 
-- 
-- ### 3.1.4 Abelian Group
-- 
-- An **Abelian group** is a group G where the binary operation is commutative, i.e., ∀ a b ∈ G, a * b = b * a. In addition to the standard group axioms (associativity, identity, and inverses), this property simplifies the structure and analysis of the group.
-- 
-- Therefore, in Lean 4, if you need to verify that a set forms an abelian (commutative) group, you must additionally verify the group axiom property that satisfies the commutative law.
-- 

-- BEGIN ORIGINAL BLOCK 011; source line 479
/- Ex6. How to define a CommGroup in Lean 4 with a Set R -/
example (R : Type u) : CommGroup (Set R) where
  -- Define the group multiplication operation
  mul := by
    sorry
  -- Prove associativity: ∀ (a b c : Set R), a * b * c = a * (b * c)
  mul_assoc := by
    sorry
  -- The identity element in Group R
  one := by
    sorry
  -- One is a left neutral element for multiplication
  one_mul := by
    sorry
  -- One is a right neutral element for multiplication
  mul_one := by
    sorry
  -- Invert an element of α, denoted by a⁻¹
  inv := by
    sorry
  -- Inverse property: ∀ (a : Set R), a⁻¹ * a = 1
  inv_mul_cancel := by
    sorry
  -- div_eq_mul_inv : ∀ (a b : Set R), a / b = a * b⁻¹
  div_eq_mul_inv := by
    sorry
  -- mul_comm : ∀ (a b : Set R), a * b = b * a
  mul_comm := by
    sorry
-- END ORIGINAL BLOCK 011

-- 
-- However, if a group structure already exists, you only need to verify that it satisfies the commutative law.
-- 

-- BEGIN ORIGINAL BLOCK 012; source line 513
/- Ex7. How to define a CommGroup in Lean 4 with a Group R -/
example (R : Type u) [Group R] : CommGroup R where
  -- This exercise requires commutativity; an arbitrary group need not have it.
  -- mul_comm : ∀ (a b : R), a * b = b * a
  mul_comm := by
    sorry
-- END ORIGINAL BLOCK 012

-- 
-- #### EX8. Let $G$ be a group in which $(a b)^{3}=a^{3} b^{3}$ and $(a b)^{5}=a^{5} b^{5}$ for all $a, b \in G$. Show that $G$ is abelian
-- 

-- BEGIN ORIGINAL BLOCK 013; source line 523
/-- EX8. Let $G$ be a group in which $(a b)^{3}=a^{3} b^{3}$ and $(a b)^{5}=a^{5} b^{5}$ for all $a, b \in G$. Show that $G$ is abelian. -/
def Group_Basic_Ex_8 {G : Type*} [Group G] (h₁ : ∀ a b : G, (a * b) ^ 3 = a ^ 3 * b ^ 3) (h₂ : ∀ a b : G, (a * b) ^ 5 = a ^ 5 * b ^ 5) : CommGroup G where
  mul_comm := by
    intro a b
    --By$(a b)^{3}=a^{3} b^{3}$, we have $$(b a)^{2}=a^{2} b^{2}  (*)$$
    have h1 : (b * a) ^ 2 = a ^ 2 * b ^ 2 := by
      calc
        _ = a⁻¹ * (a * (b * a) ^ 2 * b) * b⁻¹ := by group
        _ = a⁻¹ * (a * ((b * a) * (b * a)) * b) * b⁻¹ := by simp only [pow_two]
        _ = a⁻¹ * ((a * b) * (a * b) * (a * b)) * b⁻¹ := by group
        _ = a⁻¹ * (a * b) ^ 3 * b⁻¹ := by
          simp only [mul_left_inj, mul_right_inj]
          exact Eq.symm (pow_three' (a * b))
        _ = a⁻¹ * (a ^ 3 * b ^ 3) * b⁻¹ := by simp only [h₁]
        _ = a⁻¹ * a ^ 3 * b ^ 3 * b⁻¹ := by group
        _ = _ := by group
    --Similarly, by $(a b)^{5}=a^{5} b^{5}$, we have $$(b a)^{4}=a^{4} b^{4}  (**)$$
    have h2 : (b * a) ^ 4 = a ^ 4 * b ^ 4 := by
      calc
        _ = a⁻¹ * (a * (b * a) ^ 4 * b) * b⁻¹ := by group
        _ = a⁻¹ * (a * (b * a) ^ 3 * (b * a) * b) * b⁻¹ := by
          rw [pow_succ (b * a) 3]
          group
        _ = a⁻¹ * ((a * b) * (a * b) * (a * b) * (a * b) * (a * b)) * b⁻¹ := by
          rw [pow_three' (b * a)]
          group
        _ = a⁻¹ * (a * b) ^ 5 * b⁻¹ := by
          simp only [mul_left_inj, mul_right_inj]
          rw [← pow_three' (a * b), ← pow_succ (a * b) 3, pow_succ (a * b) 4]
        _ = a⁻¹ * (a ^ 5 * b ^ 5) * b⁻¹ := by simp only [h₂]
        _ = a⁻¹ * a ^ 5 * b ^ 5 * b⁻¹ := by group
        _ = _ := by group
    --Then, by $(*)$ and $(**)$, we have $$a^{4} b^{4}=(b a)^{4}=a^{2} b^{2} a^{2} b^{2} $$ Thus, we have $$b^{2} a^{2}=a^{2} b^{2}$$
    have h₃ : b ^ 2 * a ^ 2 = a ^ 2 * b ^ 2 := by
      calc
        _ = a⁻¹ * a⁻¹ * a * a * (b ^ 2 * a ^ 2) * b * b * b⁻¹ * b⁻¹ := by group
        _ = a⁻¹ ^ 2 * ((a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2)) * b⁻¹ ^ 2 := by group
        _ = a⁻¹ ^ 2 * (a ^ 2 * b ^ 2) ^ 2 * b⁻¹ ^ 2 := by
          simp only [inv_pow, mul_left_inj, mul_right_inj]
          exact Eq.symm (pow_two (a ^ 2 * b ^ 2))
        _ = a⁻¹ ^ 2 * ((b * a) ^ 2) ^ 2 * b⁻¹ ^ 2 := by rw [h1]
        _ = a⁻¹ ^ 2 * (b * a) ^ 4 * b⁻¹ ^ 2 := by group
        _ = a⁻¹ ^ 2 * (a ^ 4 * b ^ 4) * b⁻¹ ^ 2 := by rw [h2]
        _ = a ^ 2 * b ^ 2 := by group
    --Then, by $(*)$ and $b^{2} a^{2}=a^{2} b^{2}$, we have $$(b a)^{2}=a^{2} b^{2}=b^{2} a^{2}$$. So, we have $$a b=b a$$. $G$ is a abelian group.
    calc
      _ = b⁻¹ * ((b * a) * (b * a)) * a⁻¹ := by group
      _ = b⁻¹ * ((b * a) ^ 2) * a⁻¹ := by
        simp only [mul_left_inj, mul_right_inj]
        exact Eq.symm (pow_two (b * a))
      _ = b⁻¹ * (a ^ 2 * b ^ 2) * a⁻¹ := by rw [h1]
      _ = b⁻¹ * (b ^ 2 * a ^ 2) * a⁻¹ := by rw [h₃]
      _ = _ := by group
-- END ORIGINAL BLOCK 013

-- 
-- ### 3.1.5 Cyclic Group
-- 
-- A **cyclic group** is a group G that can be generated by a single element g ∈ G, meaning every element of G can be written as gⁿ for some integer n. Key properties include:
-- 1. **Generators**: G = ⟨g⟩ = {gⁿ | n ∈ ℤ}
-- 2. **Abelian structure**: ∀ a, b ∈ G, a * b = b * a
-- 3. **Classification**: Every cyclic group is isomorphic to either ℤ (infinite) or ℤ/nℤ (finite order n).
-- 
-- In Lean 4, a cyclic group is treated as a property rather than a standalone structure. This means you must prove that a given group satisfies the specific proposition stating it is cyclic. Similarly, for common groups like ZMod n, Lean 4 provides typeclass instances that allow automatic inference of their cyclic nature.
-- 

-- BEGIN ORIGINAL BLOCK 014; source line 588
/-- Ex9. $\mathbb{Z}$ is a cyclic group -/
theorem Group_Basic_Ex_9 : IsAddCyclic ℤ := by
  -- show that ℤ is cyclicgroup
  apply IsAddCyclic.mk
  use 1
  --1 is the generator
  intro x
  refine AddSubgroup.mem_zmultiples_iff.mpr ?h.a
  use x
  exact zsmul_int_one x

/-- Ex10. $\mathbb{Z}_{n}$ for a positive integer $n$ is a cyclic group -/
theorem Group_Basic_Ex_10 (n : ℕ) : IsAddCyclic (ZMod n) := ZMod.instIsAddCyclic n
-- END ORIGINAL BLOCK 014

-- 
-- #### Ex11. Show that Z2 × Z3 is cyclic
-- 

-- BEGIN ORIGINAL BLOCK 015; source line 606
/-- Ex11. Show that Z2 × Z3 is cyclic -/
theorem Group_Basic_Ex_11 : IsAddCyclic ((ZMod 2) × (ZMod 3)) := by
  apply isAddCyclic_of_addOrderOf_eq_card ((1 : ZMod 2), (1 : ZMod 3))
  have h1 : addOrderOf (1 : ZMod 2) = 2 := by
    exact ZMod.addOrderOf_one 2
  have h2 : addOrderOf (1 : ZMod 3) = 3 := by
    exact ZMod.addOrderOf_one 3
  let temp1 := Prod.addOrderOf ((1 : ZMod 2), (1 : ZMod 3))
  rw [h1, h2] at temp1
  rw [temp1]
  norm_num
-- END ORIGINAL BLOCK 015

-- 
-- #### Ex12. Show that Z3 × Z4 is cyclic
-- 

-- BEGIN ORIGINAL BLOCK 016; source line 622
/-- Ex12. Show that Z3 × Z4 is cyclic -/
theorem Group_Basic_Ex_12 : IsAddCyclic ((ZMod 3) × (ZMod 4)) := by
  apply isAddCyclic_of_addOrderOf_eq_card ((1 : ZMod 3), (1 : ZMod 4))
  have h1 : addOrderOf (1 : ZMod 3) = 3 := by
    exact ZMod.addOrderOf_one 3
  have h2 : addOrderOf (1 : ZMod 4) = 4 := by
    exact ZMod.addOrderOf_one 4
  let temp1 := Prod.addOrderOf ((1 : ZMod 3), (1 : ZMod 4))
  rw [h1, h2] at temp1
  rw [temp1]
  norm_num
-- END ORIGINAL BLOCK 016

-- 
-- ## 3.2 Subgroup Basic
-- 
-- A subgroup of a group G is a subset containing 1, closed under multiplication and closed under multiplicative inverse.
-- 
-- In Lean4, when we declare a subgroup, we are essentially declaring a subset of a group G that satisfies the following structural properties:
-- 
-- 1. **Closure under multiplication**: ∀ a, b ∈ H, a * b ∈ H
-- 2. **Contains the identity element**: ∃ e ∈ H such that ∀ a ∈ H, e * a = a * e = a
-- 3. **Closure under inverses**: ∀ a ∈ H, ∃ a⁻¹ ∈ H such that a * a⁻¹ = a⁻¹ * a = e
-- 

-- BEGIN ORIGINAL BLOCK 017; source line 646
/--Ex0. How to define a Subgroup in Lean 4-/
example  {G : Type*} [Group G] : Subgroup G where
  carrier := sorry
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

-- END ORIGINAL BLOCK 017

-- 
-- The definition of an additive subgroup is similar; it only requires verifying that the relevant properties hold under addition.
-- 

-- BEGIN ORIGINAL BLOCK 018; source line 658
/--Ex1. How to define a AddSubgroup in Lean 4 -/
example {G : Type*} [AddGroup G] : AddSubgroup G where
  carrier := sorry      -- The underlying subset of G
  add_mem' := sorry    -- Closure under addition: ∀ a b ∈ H, a + b ∈ H
  zero_mem' := sorry   -- Contains zero: 0 ∈ H
  neg_mem' := sorry    -- Closure under negation: ∀ a ∈ H, -a ∈ H

-- END ORIGINAL BLOCK 018

-- 
-- 
-- ### 3.2.1 Examples of how to verify it is a subgroup
-- 
-- The method of verifying a subgroup is very similar to that of verifying a group, with the difference being that you first need to specify a group and the set corresponding to this subgroup, and then check one by one whether it satisfies the required properties.
-- 
-- Here are three examples:
-- 
-- #### EX2. If $A, B$ are subgroups of $G$ such that $b^{-1} A b \subset A$ for all $b \in B$, show that $A B$ is a subgroup of $G$.
-- 

-- BEGIN ORIGINAL BLOCK 019; source line 677
section SubgroupProduct
variable {G : Type*} [Group G]
variable (A  : Subgroup G)
variable (B  : Subgroup G)

/-- def Set AB = {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b} -/
def AB: Set G := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}

/-- EX2. If $G$ is a group and $H$ a nonempty subset of $G$ such that, given $a, b \in H$, then $a b^{-1} \in H$, prove that $H$ is a subgroup of $G$. -/
example  (h : ∀ b ∈ B, ∀ a ∈ A, b⁻¹ * a * b ∈ A) : Subgroup G where
  carrier := AB A B
  mul_mem' := by
    -- For any $a, b \in AB$, we need to show that $a * b \in AB$.
    intro a b ha hb
    rw [AB]
    rw [AB] at ha hb
    simp only [Set.mem_setOf_eq] at ha hb
    rcases ha with ⟨a1, ha1, b1, hb1, h1 ⟩
    rcases hb with ⟨a2, ha2, b2, hb2, h2 ⟩
    simp only [Set.mem_setOf_eq]
    use a1 * (b1 * a2 * b1⁻¹)
    constructor
    · -- By the given condition $h$, $b1⁻¹ * a2 * b1 \in A$.
      have: (b1 * a2 * b1⁻¹) ∈ A := by
        have l1: b1 = b1⁻¹⁻¹ := by group
        nth_rw 1 [l1]
        have l2: b1⁻¹ ∈ B := by exact (Subgroup.inv_mem_iff B).mpr hb1
        exact h b1⁻¹ l2 a2 ha2
      -- Since $b1 * a2 * b1⁻¹ \in A$, we can use the closure property of $A$.
      exact (Subgroup.mul_mem_cancel_right A this).mpr ha1
    · use b1 * b2
      constructor
      · -- Since $b2 \in B$, we can use the closure property of $B$.
        exact (Subgroup.mul_mem_cancel_right B hb2).mpr hb1
      · -- We need to show that $a1 * (b1 * a2 * b1⁻¹) * b1 * b2 = a * b$.
        rw [h1, h2]
        group
  one_mem' := by
    -- We need to show that $1 \in AB$.
    rw [AB]
    simp only [Set.mem_setOf_eq]
    use 1
    constructor
    · -- The identity element $1 \in A$.
      exact Subgroup.one_mem A
    · use 1
      constructor
      · -- The identity element $1 \in B$.
        exact Subgroup.one_mem B
      · -- The identity element $1$ satisfies $1 * 1 = 1$.
        rw [mul_one]
  inv_mem' := by
    -- For any $x \in AB$, we need to show that $x⁻¹ \in AB$.
    intro x
    rw [AB]
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro a ha b hb hab
    use b⁻¹ * a⁻¹ * b
    constructor
    · -- By the given condition $h$, $b⁻¹ * a⁻¹ * b \in A$.
      have: a⁻¹ ∈ A := by exact (Subgroup.inv_mem_iff A).mpr ha
      exact h b hb a⁻¹ this
    · use b⁻¹
      constructor
      · -- Since $b \in B$, $b⁻¹ \in B$.
        exact (Subgroup.inv_mem_iff B).mpr hb
      · -- We need to show that $(a * b)⁻¹ = b⁻¹ * a⁻¹ * b$.
        rw [hab]
        group
end SubgroupProduct
-- END ORIGINAL BLOCK 019

-- 
-- #### EX3. Prove that if $G$ is an abelian group, written multiplicatively, with identity element $e$, then all elements $x$ of $G$ satisfying the equation $x^{2}=e$ form a subgroup $H$ of $G$.
-- 
-- 

-- BEGIN ORIGINAL BLOCK 020; source line 753
/-- EX3. Prove that if $G$ is an abelian group, written multiplicatively, with identity element $e$, then all elements $x$ of $G$ satisfying the equation $x^{2}=e$ form a subgroup $H$ of $G$. -/
def EX3  (G : Type*)[CommGroup G] : Subgroup G where
  carrier := { g : G | g * g = (1 : G)}
  --1. In order to prove it is a subgroup, we should vertify its closure on mul.
  mul_mem' := by
   intro x y hx hy
   have x_y : (x * y) * (x * y) = 1 :=by
   --2. We can easily have that $x*y*(x*y)=x*y*y*x=1$
     rw[← hx,mul_assoc]
     apply mul_left_cancel_iff.mpr
     nth_rw 2 [← mul_one x]
     rw[← hy,← mul_assoc,← mul_assoc]
     apply mul_right_cancel_iff.mpr
     rw[mul_comm]
   exact x_y
  one_mem' := by
   show 1 * 1 = 1
   --3. We should the one in it which is obvious for $1*1=1$
   group
  inv_mem' := by
   intro x hx
   have x_eq_inv : x = x⁻¹ := by rw[← mul_one x⁻¹, ← hx,← mul_assoc, inv_mul_cancel,one_mul]
   have x_inv : x⁻¹  * x⁻¹  = (1:G) :=by rw[← x_eq_inv,hx]
   --4. We should vertify the inv by using $x^{-1}*x^{-1}=x*x=1$
   exact x_inv

-- END ORIGINAL BLOCK 020

-- 
-- #### EX4. Show that $n \mathbb{Z}$ is a subgroup of the additive group of integers $\mathbb{Z}$, for all integers $n$.
-- 
-- 

-- BEGIN ORIGINAL BLOCK 021; source line 785
/-- EX4. Show that $n \mathbb{Z}$ is a subgroup of the additive group of integers $\mathbb{Z}$, for all integers $n$. -/
def EX4 (n : ℕ) : AddSubgroup ℤ where
  carrier := { x | ∃ k , x = n * k }
 --First we define nℤ, the subset of addgroup ℤ
  add_mem' := by
 --Prove that nℤ is closed to addition
   intro a b
   dsimp
  --Simplify the goal we want to prove
   intro h hx
  --Denote the conditions as h and hx
   rcases h with ⟨k₁ , h'⟩
  --Let the existing k be k₁ and denote the new condition as h'
   rcases hx with ⟨k₂ , hx'⟩
  --Let the existing k be k₂ and denote the new condition as hx'
   use k₁ + k₂
  --Let k be k₁ + k₂
   ring_nf
   rw[h' , hx']
  --From the distributive property and h', hx' we can draw the conclusion
  zero_mem' := by
   dsimp
  --Simplify the goal we want to prove
   use 0
   group
  --Just by letting k be 0 and using the property of group we can draw the conclusion
  neg_mem' := by
   intro a
   dsimp
  --Simplify the goal we want to prove
   intro h
  --Denote the conditions as h
   rcases h with ⟨k₁, h'⟩
  --Let the existing k be k₁ and denote the new condition as h'
   use -k₁
  --Let k be -k₁
   group
   rw [h']

-- END ORIGINAL BLOCK 021

-- 
-- Based on the different properties satisfied by the corresponding subset within a group, we can naturally define several common subgroup structures, such as the center of a group, normal subgroups, the centralizer of a subgroup, and other familiar concepts.
-- 
-- ### 3.2.2 Normal Subgroup
-- 
-- A **normal subgroup** of a group $G$ is a subgroup $N$ that is closed under conjugation by elements of $G$. Formally, $N$ is normal if:
-- 1. **Conjugation invariance**: ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N
-- 2. **Equivalently**, N satisfies gN = Ng for all g ∈ G, meaning left and right cosets coincide.
-- 
-- Normal subgroups are essential in constructing quotient groups $G/N$ and studying group homomorphisms via the First Isomorphism Theorem. They arise naturally in symmetry analysis and algebraic structures.
-- 
-- Verifying that a subgroup is a normal subgroup is accomplished by checking that it satisfies the defining properties.
-- 
-- Additionally, the normalizer of a subgroup $H$ in a group $G$ is the largest subgroup of $G$ that contains $H$ as a normal subgroup. The normalizer itself naturally forms a subgroup.
-- 

-- BEGIN ORIGINAL BLOCK 022; source line 841
/-- EX5. Verify that H is a normal subgroup of G -/
theorem Group_Subgroup_Ex_5 {G : Type u} [Group G] (H : Subgroup G) : H.Normal :=by
  sorry

/-- EX6. The normalizer of Subgroup H as a Subgroup of G -/
def Group_Subgroup_Ex_6 {G : Type u} [Group G] (H : Subgroup G) : Subgroup G := H.normalizer
-- END ORIGINAL BLOCK 022

-- 
-- #### EX7. Show that if $H$ is a subgroup with $b H=H b=\{h b: h \in H\}$ for every $b \in G$, then $H$ must be a normal subgroup.
-- 

-- BEGIN ORIGINAL BLOCK 023; source line 852
/-- EX7. Show that if $H$ is a subgroup with $b H=H b={h b: h \in H}$ for every $b \in G$, then $H$ must be a normal subgroup. -/
theorem Group_Subgroup_Ex_7 {G : Type*} [Group G] {H : Subgroup G} (h₀ : ∀ b : G, {h * b | h : H} = {b * h | h : H}) : H.Normal where
  -- We just have to prove that $\forall g \in G$ and $\forall h \in H, \ ghg^{-1} \in H$.
  conj_mem := by
    intro h hh g
    have hg := h₀ g
    apply Set.Subset.antisymm_iff.mp at hg
    rcases hg with ⟨_, hg⟩
    -- Since $gh \in gH = Hg$, we know that $\exists h' \in H, \ gh = h'g$.
    have h₁ : g * h ∈ {x | ∃ h : H, g * h = x} := by
      apply Set.mem_setOf.mpr
      use ⟨h, hh⟩
    have h₂ := hg h₁
    apply Set.mem_setOf.mp at h₂
    rcases h₂ with ⟨h', hh'⟩
    -- Hence, $ghg^{-1} = h' \in H$, so $H$ is a normal subgroup of $G$.
    rw [← hh', mul_assoc, mul_inv_cancel, mul_one]
    exact SetLike.coe_mem h'

-- END ORIGINAL BLOCK 023

-- 
-- #### EX8. If $N \triangleleft G$ and $H$ is a subgroup of $G$, show that $H \cap N \triangleleft H$.
-- 

-- BEGIN ORIGINAL BLOCK 024; source line 876
/-- EX8. If $N \triangleleft G$ and $H$ is a subgroup of $G$, show that $H \cap N \triangleleft H$. -/
theorem Group_Subgroup_Ex_8 (G : Type) [Group G] (N H : Subgroup G) (hn : N.Normal) : ((H ⊓ N).subgroupOf H).Normal := by
  --To prove that $H \cap N \lhd H$, we just need to prove that $H \cap N \le H$ and then prove that $H \cap N$ is a normal subgroup of H.
  refine (Subgroup.normal_subgroupOf_iff ?hHK).mpr ?_
  --Firstly, we know that $H \cap N \sube H$ and that $H \cap N$ is a group, then obviously, $H \cap N \le H$.
  · simp only [inf_le_left]

  --Then, we just need to prove that for $\forall a \in H \cap N$, $\forall h \in H$, $hah^{-1} \in H$ and that $hah^{-1} \in N$.
  · intro g k gHN kH
    simp only [Subgroup.mem_inf]
    constructor

    --But for $\forall a \in H \cap N$, obviously $a \in H$, then for $\forall h \in H$, $hah^{-1} \in H$.
    · have h₁ : g ∈ H := by
        simp only [Subgroup.mem_inf] at gHN
        exact gHN.1

      have h₂ : k⁻¹ ∈ H := by exact (Subgroup.inv_mem_iff H).mpr kH
      have : k * g ∈ H := by exact (Subgroup.mul_mem_cancel_right H h₁).mpr kH
      exact (Subgroup.mul_mem_cancel_right H h₂).mpr this

    --Also, because $N \lhd G$, so $\forall a \in H\cap N$(definitely we have $a \in N$), $hah^{-1} \in N$, thus finishing the proof. $\square$
    · have h₁ : g ∈ N := by
        simp only [Subgroup.mem_inf] at gHN
        exact gHN.2

      exact hn.conj_mem g h₁ k
-- END ORIGINAL BLOCK 024

-- 
-- ### 3.2.3 Center
-- 
-- The **center of a group** G, denoted Z(G), is the set of elements that commute with every element of G. Formally, Z(G) = {z ∈ G | ∀ g ∈ G, z * g = g * z}. Key properties include:
-- 1. **Subgroup structure**: Z(G) is always a normal subgroup of G.
-- 2. **Abelian connection**: If Z(G) = G, then G is abelian.
-- 
-- The center is crucial in group theory for analyzing commutativity and decomposing groups via central quotients.
-- 
-- **Centralizer** of a subset S in a group G is the set of elements in G that commute with every element of S. Formally, the centralizer C(S) is defined as C(S) = {g ∈ G | ∀ s ∈ S, g * s = s * g}. Key properties include:
-- 1. **Subgroup structure**: C(S) is always a subgroup of G
-- 2. **Relation to center**: If S = G, then C(G) = Z(G), the center of G
-- 

-- BEGIN ORIGINAL BLOCK 025; source line 918
/-- EX9. Verify that $Z(G)$, the center of $G$, is a subgroup of $G$. (See Example 11.) -/
def Group_Subgroup_Ex_9 {G : Type*} [Group G] : Subgroup G where
  carrier := Subgroup.center G
  -- 1. Closure under multiplication:
  mul_mem' := by
    -- To show: ∀ a b ∈ Z(G), ∀ g : G, g * a * b = a * b * g
    intro a b ha hb
    apply Semigroup.mem_center_iff.mpr
    intro g
    -- We have g * a * b = a * g * b = a * b * g, so it holds
    rw [← mul_assoc, ← ha.comm, mul_assoc, ← hb.comm, ← mul_assoc]
  -- 2. Contains the identity:
  one_mem' := by
    -- To show: ∀ g : G, g * 1 = 1 * g
    apply Semigroup.mem_center_iff.mpr
    intro g
    -- We have g * 1 = g = 1 * g, which holds
    rw [mul_one, one_mul]
  -- 3. Closure under inverses:
  inv_mem' := by
    -- To show: ∀ x ∈ Z(G), ∀ g : G, g * x⁻¹ = x⁻¹ * g
    intro x hx
    apply Semigroup.mem_center_iff.mpr
    intro g
    -- We have g * x⁻¹ = (x * g⁻¹)⁻¹ = (g⁻¹ * x)⁻¹ = x⁻¹ * g, which holds
    rw [← inv_inv g, ← mul_inv_rev, hx.comm, mul_inv_rev]


/-- EX10. Find $C(4)$ in $\mathbb{Z}_{7}$. -/
theorem Group_Subgroup_Ex_10 : AddSubgroup.centralizer ({4} :Set (ZMod 7)) = ⊤ := by
  ext x
  constructor
  · exact fun _ ↦ trivial
  · intro _ y
    exact fun _ ↦ AddCommMagma.add_comm y x
-- END ORIGINAL BLOCK 025

-- 
-- #### EX11. If $H$ is a subgroup of $G$, then show that $Z(G) \cap H$ is a subgroup of $Z(H)$.
-- 

-- BEGIN ORIGINAL BLOCK 026; source line 958
/-- EX11. If $H$ is a subgroup of $G$, then show that $Z(G) \cap H$ is a subgroup of $Z(H)$. -/
def Group_Subgroup_Ex_11 {G : Type*} [Group G]  (H : Subgroup G): Subgroup (Subgroup.center H) where
  carrier := {g | g.1.1 ∈ Subgroup.center G}
  --we prove that $Z(G) \cap H$ is a group. Get $a,b$ from $Z(G) \cap H$, then $a*b \in H$, and $\forall g \in G, (a*b)*g=a*g*b=g*a*b$, which means that $a*b \in Z(G)$.
  mul_mem':=by
    intro a b ha hb
    simp only [Set.mem_setOf_eq]
    simp only [Set.mem_setOf_eq] at ha
    simp only [Set.mem_setOf_eq] at hb
    have : ∀ g :G, (a.1.1* b.1.1)*g = g* (a.1.1 * b.1.1):=by
      intro g
      have t1:∀ g : G , a.1.1 * g = g *a.1.1:=by exact fun g => ha.comm g
      have t2:∀ g : G , b.1.1 * g = g *b.1.1:=by exact fun g => hb.comm g
      let i:= t1 g
      let j:= t2 g
      rw[mul_assoc,j,← mul_assoc, i]
      group
    exact (Subgroup.mul_mem_cancel_right (Subgroup.center G) hb).mpr ha
  --It is obvious that $1\in H$ and $1\in Z(G)$.
  one_mem':=by
    simp only [Set.mem_setOf_eq, OneMemClass.coe_one]
    exact Subgroup.one_mem (Subgroup.center G)
  -- Get $a$ from $Z(G) \cap H$, then $a^{-1} \in H$ and $\forall g \in G, g*a^{-1}=(a*g^{-1})^{-1}=(g^{-1}*a)^{-1}=a^{-1}*g$. And $a^{-1} \in Z(G)$.
  inv_mem':=by
    simp only [Set.mem_setOf_eq, InvMemClass.coe_inv, inv_mem_iff,
      imp_self, implies_true]

-- END ORIGINAL BLOCK 026

-- 
-- #### EX12. Prove that $C_{G}(Z(G))=G$ and deduce that $N_{G}(Z(G))=G$.
-- 

-- BEGIN ORIGINAL BLOCK 027; source line 992
/-- EX12. Prove that $C_{G}(Z(G))=G$ and deduce that $N_{G}(Z(G))=G$. -/
lemma centralizer_center_eq_self {G : Type*} [Group G] : Subgroup.centralizer (Subgroup.center G : Set G) = ⊤ := by
  ext g
  apply Iff.intro
  · -- we show that C_G(Z(G)) ⊆ G.
    show g ∈ Subgroup.centralizer ↑(Subgroup.center G) → g ∈ ⊤
    -- This is trivial because C_G(Z(G)) is defined as a subset of G (it consists of elements of G that commute with elements of Z(G))
    intro h
    trivial
  · -- we show that g ∈ C_G(Z(G)).
    show g ∈ ⊤ → g ∈ Subgroup.centralizer ↑(Subgroup.center G)
    -- by definition of centralizer, we need to show that g commutes with every element of Z(G)
    simp [Subgroup.center];
    intro z hz;
    -- By the definition of the center Z(G), every element z∈Z(G) commutes with g, i.e.,zg = gz.
    exact hz.comm _
/-- Prove that C_G(Z(G)) = N_G(Z(G)) -/
lemma centralizer_center_eq_normalizer_center {G : Type*} [Group G]: Subgroup.centralizer (Subgroup.center G : Set G) = Subgroup.setNormalizer (Subgroup.center G)  := by
  -- By the definition of centralizer and normalizer, we need to show that g commutes with every element of Z(G) if and only if g normalizes Z(G).
  ext g
  simp [Subgroup.setNormalizer, Subgroup.center]
  show (∀ z ∈ Set.center G, z * g = g * z) ↔ ∀ (n : G), n ∈ Set.center G ↔ g * n * g⁻¹ ∈ Set.center G
  apply Iff.intro
  · -- We show that if g commutes with every element of Z(G), then g normalizes Z(G).
    show (∀ z ∈ Set.center G, z * g = g * z) → ∀ (n : G), n ∈ Set.center G ↔ g * n * g⁻¹ ∈ Set.center G
    intros h z
    apply Iff.intro
    · -- We show that if z ∈ Z(G), then g * z * g⁻¹ ∈ Z(G).
      show z ∈ Set.center G → g * z * g⁻¹ ∈ Set.center G
      specialize h z
      intro this
      simpa [←(h this)] using this
    · -- We show that if g * z * g⁻¹ ∈ Z(G), then z ∈ Z(G).
      show g * z * g⁻¹ ∈ Set.center G → z ∈ Set.center G
      specialize h (g * z * g⁻¹); simp at h;
      -- We need prove that g * z * g⁻¹ ∈ Z(G) implies z ∈ Z(G).
      show g * z * g⁻¹ ∈ Set.center G → z ∈ Set.center G
      intro this;
      simpa [←(h this)] using this
  · -- We show that if g normalizes Z(G), then g commutes with every element of Z(G).
    show (∀ (n : G), n ∈ Set.center G ↔ g * n * g⁻¹ ∈ Set.center G) → ∀ z ∈ Set.center G, z * g = g * z
    intro h z hz
    -- By the definition of the center Z(G), every element z∈Z(G) commutes with g, i.e.,zg = gz.
    exact hz.comm g
/-- Deduce that N_G(Z(G)) = G -/
theorem Group_Subgroup_Ex_12 {G : Type*} [Group G] :Subgroup.setNormalizer (Subgroup.center G : Set G) = ⊤ := by
  rw [←centralizer_center_eq_normalizer_center]
  rw [centralizer_center_eq_self]
-- END ORIGINAL BLOCK 027

-- 
-- ## 3.3 Quotient Groups
-- 
-- ### 3.3.1 Basic Definition about Quotient Groups
-- 
-- A **quotient group** (also called a **factor group**) is formed by partitioning a group $G$ into cosets of a normal subgroup $N \trianglelefteq G$, and defining a group structure on the set of these cosets.
-- 
-- Formally, if $G$ is a group and $N$ is a normal subgroup of $G$, then the quotient group $G / N$ is the set of all left cosets:
-- $$
-- G / N = \{ gN \mid g \in G \}
-- $$
-- with the group operation defined as:
-- $$
-- (gN) \cdot (hN) = (gh)N
-- $$
-- 
-- This operation is **well-defined** if and only if $N$ is a **normal subgroup** of $G$.
-- 
-- In Lean 4, defining a quotient group typically requires providing an instance that the subgroup is normal. The elements of the quotient group can be represented using `QuotientGroup.mk'`, which essentially gives a homomorphism from the group to the quotient group.
-- 

-- BEGIN ORIGINAL BLOCK 028; source line 1062

-- Ex. Property of the Quotient Group
example (G : Type u)[Group G](N : Subgroup G)(hN : N.Normal)(a b : G) :
QuotientGroup.mk' N (a * b) = QuotientGroup.mk' N a * QuotientGroup.mk' N b :=by
  exact rfl

example (G : Type u)[Group G](N : Subgroup G)(hN : N.Normal)(a b : G):
QuotientGroup.mk' N (a * b) = QuotientGroup.mk' N a * QuotientGroup.mk' N b := by
  exact rfl

example (G : Type u)[Group G](N : Subgroup G)(hN : N.Normal)(a : G):
QuotientGroup.mk' N a = 1 ↔ a ∈ N := by
  apply QuotientGroup.eq_one_iff

-- END ORIGINAL BLOCK 028

-- 
-- ### 3.3.2 Examples about how to calculate in Quotient Group
-- 
-- Next, we provide several examples of performing calculations with elements in the quotient group, using elements from `ℝ/ℤ` as illustrations.
-- 

-- BEGIN ORIGINAL BLOCK 029; source line 1083
-- Ex. Verify 7 / 2 = 1 / 2 in ℝ ⧸ ℤ
example : ((7 / 2 : ℝ) : ℝ ⧸ (Int.castAddHom ℝ).range)  =  ((1 / 2 : ℝ) : ℝ ⧸ (Int.castAddHom ℝ).range) := by
  rw [QuotientAddGroup.eq]
  norm_cast; simp [AddSubgroup.mem_zmultiples_iff]
  use -3
  norm_num

-- Ex. Verify 7 / 2 = 1 / 2 in ℝ ⧸ ℤ
example : (QuotientAddGroup.mk' (Int.castAddHom ℝ).range) (7 / 2 : ℝ) = (QuotientAddGroup.mk' (Int.castAddHom ℝ).range) (1 / 2 : ℝ) :=by
  rw [QuotientAddGroup.mk'_eq_mk']
  use -3
  constructor
  . norm_cast; simp [AddSubgroup.mem_zmultiples_iff]
    use 3
    exact rfl
  . norm_num

-- Ex. Verify 3 + 1 / 2 = 1 / 2 in ℝ ⧸ ℤ
example  : ( ((3 : ℝ) : ℝ ⧸ (Int.castAddHom ℝ).range) +  ((1 / 2 : ℝ) : ℝ ⧸ (Int.castAddHom ℝ).range)) =  ((1 / 2 : ℝ) : ℝ ⧸ (Int.castAddHom ℝ).range) := by
  norm_cast; simp [AddSubgroup.mem_zmultiples_iff]
  use 3
  exact rfl

-- END ORIGINAL BLOCK 029

-- 
-- #### EX13. Find the order of the element $\frac{1}{2}+\mathbb{Z}$ in $G$.
-- 

-- BEGIN ORIGINAL BLOCK 030; source line 1111
/-- It is possible to have a group that has elements of any order. Let $G=\mathbb{R}/\mathbb{Z}$.
 Find the order of the element $\frac{1}{2}+\mathbb{Z}$ in $G$. -/
theorem order_two : addOrderOf ((1 / 2 : ℝ) : ℝ ⧸ (Int.castAddHom ℝ).range) = 2 := by
  -- use the definition of orders
  refine (addOrderOf_eq_iff (show 0 < (2 : ℕ) by decide)).mpr ⟨?_, ?_⟩
    -- prove multiplication by $2$ cancels the element
  · norm_cast; simp only [one_div]
    rw [← QuotientAddGroup.mk_nat_mul]
    simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
      QuotientAddGroup.eq_zero_iff, Int.range_castAddHom, AddSubgroup.mem_zmultiples]
  · intro m hm hm'
    -- The only positive exponent below 2 is 1.
    have : m = 1 := by omega
    subst m
    rw [one_smul, ne_eq, QuotientAddGroup.eq_zero_iff]
    -- A zero coset would make 1/2 the image of an integer.
    rintro ⟨x, hx⟩
    change (x : ℝ) = 1 / 2 at hx
    by_cases l : x ≤ 0
    · -- A non-positive integer cannot equal 1/2.
      have : (x : ℝ) ≤ 0 := Int.cast_nonpos.mpr l
      linarith
    · -- A positive integer is at least 1, so it cannot equal 1/2 either.
      have l : 1 ≤ x := by omega
      have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast l
      linarith

-- END ORIGINAL BLOCK 030

-- 
-- ## 3.4 Sylow $p$-Subgroups
-- 
-- ### 3.4.1 Basic Definition of Sylow $p$-Subgroups
-- 
-- Let $G$ be a finite group, and let $p$ be a prime number. A **Sylow $p$-subgroup** of $G$ is a maximal $p$-subgroup of $G$, meaning a subgroup whose order is a power of $p$, and which is not properly contained in any larger $p$-subgroup of $G$.
-- 
-- Formally, let $|G| = p^n \cdot m$ with $p \nmid m$, then a subgroup $P \leq G$ is called a **Sylow $p$-subgroup** if:
-- 
-- - $|P| = p^n$, and
-- - $P$ is a subgroup of $G$.
-- 
-- We denote the set of all Sylow $p$-subgroups of $G$ by $\mathrm{Syl}_p(G)$.
-- 
-- 

-- BEGIN ORIGINAL BLOCK 031; source line 1166
-- Ex. Verify that it is a sylow p Subgroup
example {G : Type u_1} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
(H : Subgroup G) (card_eq : Nat.card ↥H = p ^ (Nat.card G).factorization p):
↑(Sylow.ofCard H card_eq) = H := by
  apply Sylow.coe_ofCard

-- END ORIGINAL BLOCK 031

-- 
-- ---
-- 
-- ### 3.4.2 Sylow Theorems
-- 
-- The **Sylow theorems** provide deep information about the existence, conjugacy, and number of Sylow $p$-subgroups in a finite group.
-- 
-- #### **Sylow’s First Theorem (Existence)**
-- 
-- Let $G$ be a finite group and $|G| = p^n \cdot m$ with $p \nmid m$. Then here exists a subgroup $P \leq G$ such that $|P| = p^n$.
-- 
-- Such a subgroup is a Sylow $p$-subgroup.
-- 

-- BEGIN ORIGINAL BLOCK 032; source line 1187
-- Ex. Verify Sylow-first theorem
example {G : Type u} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact (Nat.Prime p)]
(hdvd : p ^ n ∣ Nat.card G) : ∃ (K : Subgroup G), Nat.card ↥K = p ^ n := by
  simp [Sylow.exists_subgroup_card_pow_prime, hdvd]

-- END ORIGINAL BLOCK 032

-- 
-- Let's use an example to illustrate how to apply Sylow's theorems to prove propositions related to normal subgroups. This example vividly illustrates how Sylow's theorem is particularly effective in dealing with problems related to the order of groups.
-- 

-- BEGIN ORIGINAL BLOCK 033; source line 1197
-- Ex. Use Sylow-first theorem to prove

/-- Lemma: Index of Sylow p-group is $|G|/p^k$. -/
lemma index_sylow_eq_ord_compl{G : Type*} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    P.index = Nat.card G / p ^ (Nat.card G).factorization p := by
  apply Nat.eq_div_of_mul_eq_left
  . -- It is obvious that $p^k$ is not $0$.
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  . -- $[G:P]*|P| = |G|$
    rw [mul_comm]
    convert Subgroup.card_mul_index (P : Subgroup G)
    exact (Sylow.card_eq_multiplicity P).symm
/--Lemma : Card of S_{5} is 120  -/
lemma Card_of_S5 : Nat.card (Perm (Fin 5)) = 120 :=by
  rw [Nat.card_perm]
  norm_num
/-- Fact of Prime 5 -/
instance : Fact (Nat.Prime 5) := Fact.mk (by decide)
/-- For p = 2, we have Nat.card (Sylow 2 (Perm (Fin 5))) = 1 or 3 or 5 or 13.  -/
lemma Unexplored_2450_8_P2 :
    Nat.card (Sylow 2 (Perm (Fin 5))) = 1 ∨ Nat.card (Sylow 2 (Perm (Fin 5))) = 3 ∨ Nat.card (Sylow 2 (Perm (Fin 5))) = 5 ∨ Nat.card (Sylow 2 (Perm (Fin 5))) = 15 :=by
  -- show that card of Perm (Fin 5) is 120
  have cardS : Nat.card (Perm (Fin 5)) = 120 := by apply Card_of_S5
  -- Sylow 2-subgroup of $  S_{5} $ satisfies Nat.card (Sylow 3 S_{5}) | 15
  have sy2_dvd_index := Sylow.card_dvd_index (default : Sylow 2 (Perm (Fin 5)))
  rw [index_sylow_eq_ord_compl, cardS, show Nat.factorization 120 2 = 3 by decide +native,
    show 120 / 2 ^ 3 = 15 by omega] at sy2_dvd_index
  -- show that Sylow 7-subgroup belongs to divisors of 6
  have mem_divisors15 : Nat.card (Sylow 2 (Perm (Fin 5))) ∈ Nat.divisors 15 := by
    rw [Nat.mem_divisors]; exact ⟨sy2_dvd_index, by norm_num⟩
  simp [show Nat.divisors 15 = {1, 3, 5, 15} by decide, -Nat.card_eq_fintype_card] at mem_divisors15
  exact mem_divisors15

-- END ORIGINAL BLOCK 033

-- 
-- ### 3.4.3 Examples about Sylow theorems
-- 
-- #### EX1. If $P$ is a $p$-Sylow subgroup of $G$ and $P \triangleleft G$, prove that $P$ is the only $p$-Sylow subgroup of $G$.
-- 

-- BEGIN ORIGINAL BLOCK 034; source line 1237
/--Let $P$ be a $p$-Sylow subgroup of $G$ and suppose $P$ is normal in $G$. We need to prove that $P$ is the only $p$-Sylow subgroup of $G$. -/
noncomputable example {G : Type*} [Group G]{p : ℕ} [Fact p.Prime] [Finite (Sylow p G)](P : Sylow p G) (h : P.Normal) : Unique (Sylow p G) := by
  -- By the corollary of the Sylow theorem, if $P$ is a normal subgroup of $G$ and $P$ is a $p$-Sylow subgroup, then $P$ is the unique $p$-Sylow subgroup of $G$.
  exact Sylow.unique_of_normal P h

-- END ORIGINAL BLOCK 034

-- 
-- #### EX2. Let $P$ be a normal Sylow $p$-subgroup of $G$ and let $H$ be any subgroup of $G$. Prove that $P \cap H$ is the unique Sylow $p$-subgroup of $H$.
-- 

-- BEGIN ORIGINAL BLOCK 035; source line 1247
/-- Let $P$ be a normal Sylow $p$-subgroup of $G$ and let $H$ be any subgroup of $G$. Prove that $P \cap H$ is the unique Sylow $p$-subgroup of $H$. -/
-- We start by proving that the intersection of $P$ and $H$ is indeed a Sylow $p$-subgroup of $H$.
def inf_sylow {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (PN : P.Normal) : Sylow p H where
  carrier := (P.subgroupOf H)
  mul_mem' := mul_mem
  one_mem' := one_mem (P.subgroupOf H)
  inv_mem' := inv_mem
  isPGroup' := by
    -- First, we need to show that $(P \cap H)$ is indeed a $p$-group.
    apply IsPGroup.iff_card.mpr
    -- Suppose $|P| = p ^ n$ since $P$ is a $p$-group,
    rcases P with ⟨P, IsP, PMax⟩
    rcases (IsPGroup.exists_card_eq IsP) with ⟨n, card_P⟩
    -- and we can let $|P| = |P \cap H| \cdot k$ because $P \cap H$ is a sugroup of $P$.
    rcases (Subgroup.card_subgroup_dvd_card (H.subgroupOf P)) with ⟨k, hk⟩
    -- $p ^ n = k |P \cap H|$.
    rw [card_P] at hk
    have : Nat.card (P.subgroupOf H) = Nat.card (H.subgroupOf P) := by
      rw [← Subgroup.inf_subgroupOf_left P H, ← Subgroup.inf_subgroupOf_right H P]
      apply Nat.card_congr (Equiv.trans (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv.symm)
    change ∃ m : ℕ, Nat.card (P.subgroupOf H) = p ^ m
    rw [this]
    -- From $p ^ n = k |P \cap H|$ we know $|P \cap H| = p ^ m$ for some $m \in \N$, hence $|P \cap H|$ is a $p$-group.
    rcases (Nat.dvd_prime_pow Fact.out).mp (dvd_of_mul_right_eq k hk.symm) with ⟨m, _, hm⟩
    exact ⟨m, hm⟩
  -- Next, we show that $(P \cap H)$ is a maximal $p$-subgroup of $H$.
  is_maximal' := by
    -- Notice the normal subgroup $P$ is the unique Sylow $p$-subgroup of $G$.
    have PU : Unique (Sylow p G) := Sylow.unique_of_normal P PN
    -- Suppose there's a Sylow $p$-subgroup $Q$ of $H$ and $P \cap H \subseteq Q$, we aim to prove $P \cap H = Q$.
    intro Q Qpg PleQ
    set Q' := Subgroup.map H.subtype Q with hQ'
    have Q'pg : IsPGroup p Q' := IsPGroup.map Qpg H.subtype
    -- By Sylow's theorem, $Q$ is contained in some Sylow $p$-subgroup $P'$ of G,
    rcases (IsPGroup.exists_le_sylow Q'pg) with ⟨P', hP'⟩
    -- but from the uniqueness we know $P' = P$.
    have PeqP' : P = P' := le_antisymm le_of_subsingleton le_of_subsingleton
    rw [← PeqP'] at hP'
    -- Hence $Q \subseteq P' = P$, combining the hypothesis we are done.
    apply le_antisymm _ PleQ; show Q ≤ (P.subgroupOf H)
    have : (Q'.subgroupOf H) ≤ (P.subgroupOf H) := (fun _ x => hP' x)
    apply le_trans _ this; rw [hQ']
    intro x hx; exact ⟨x, hx, rfl⟩
-- The uniqueness of $P \cap H$ follows from the fact that $P \cap H$ is normal since $P$ is normal.
noncomputable def unique_inf_sylow {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (PN : P.Normal) : Unique (Sylow p H) := Sylow.unique_of_normal (inf_sylow H p P PN) Subgroup.normal_subgroupOf

-- END ORIGINAL BLOCK 035

-- #### EX3. Let $Q$ be a normal $p$-subgroup of a finite group $G$. Prove that $Q \leq P$ for every Sylow $p$-subgroup $P$ of $G$.
-- 

-- BEGIN ORIGINAL BLOCK 036; source line 1296
/--If $Q$ is a normal subgroup of $G$ and $Q$ is a $p$-group, then $Q$ is contained in every Sylow $p$-subgroup of $G$.-/
theorem Q_normalp_contained_in_each_Sylp {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (Q : Subgroup G)
(h_normal : Q.Normal) (h_pgroup : IsPGroup p Q) : ∀ P : Sylow p G, Q ≤ P := by
  -- Given any Sylow $p$ group $P$ of $G$,
  intro P
  -- By Sylow first theorem, there exists a Sylow $p$ group $P_1$
  --s.t., $H \leq P_1$.
  have Q_in_sylow_p := IsPGroup.exists_le_sylow h_pgroup
  rcases Q_in_sylow_p with ⟨P₁, hP₁⟩
  -- By Sylow second theorem, $P$ is conjugates to $P_1$
  have sylow_conj_same := (Sylow.isPretransitive_of_finite (p := p) (G := G))
  -- That is, there exists a $g \in G$, s.t., $g \cdot P_1 = P$
  replace sylow_conj_same := sylow_conj_same.1 P₁ P
  rcases sylow_conj_same with ⟨g, hg⟩
  -- By the normality of $Q$, $g \cdot Q = Q$
  rw [← hg, ← Subgroup.Normal.conjAct h_normal g]
  -- Thus $N \leq P_1 \Rightarrow N = g \cdot N \leq g \cdot P_1 = P$
  rw [← @Subgroup.pointwise_smul_le_pointwise_smul_iff _ _ _ _ ConjAct.instMulDistribMulAction g] at hP₁
  convert hP₁

-- END ORIGINAL BLOCK 036

-- ---
-- 
-- 
-- 
-- 
-- ## 3.5 Group Homomorphism
-- 
-- ### 3.5.1 Basic Definition of Group Homomorphism
-- 
-- A **group homomorphism** is a function between two groups that preserves the group operation.
-- 
-- Formally, let $(G, \cdot)$ and $(H, *)$ be groups. A function $f : G \to H$ is called a **group homomorphism** if for all $a, b \in G$:
-- $$
-- f(a \cdot b) = f(a) * f(b)
-- $$
-- 
-- This property ensures that the structure of $G$ is "respected" by the function $f$ when mapping into $H$.
-- 
-- If $f$ is also **bijective**, it is called a **group isomorphism**, and $G$ and $H$ are said to be **isomorphic** groups. Below demonstrates the strategy for declaring a group homomorphism/group isomorphism in mathlib according to the definition.
-- 

-- BEGIN ORIGINAL BLOCK 037; source line 1338
-- Ex 3.5.1 How to define a Group Homomorphism
def ex5_1 {G : Type*}(h : CommGroup G) : G →* G := {
    toFun := λ a => a⁻¹
    map_one' := inv_one
    map_mul' := by
      intro a b
      show (a * b)⁻¹ = a⁻¹ * b⁻¹
      exact mul_inv a b
    }

-- Ex 3.5.1 How to define a Group Isomorphism
def ex5_1_iso {G : Type*} [Group G] : G ≃* G := {
  toFun := λ a => a,
  invFun := λ a => a,
  left_inv := λ a => rfl,
  right_inv := λ a => rfl,
  map_mul' := by
    intro a b
    rfl
  }

-- END ORIGINAL BLOCK 037

-- 
-- In practical scenarios, verifying isomorphisms strictly by definition can be overly cumbersome. In later chapters, we will introduce alternative strategies for proving isomorphisms.
-- 
-- Generally speaking, the most common approach to proving homomorphisms/isomorphisms is to explicitly construct the corresponding function according to their definitions. Alternatively, for certain special problems, one may directly apply relevant theorems. For example, one can demonstrate that a group homomorphism is an isomorphism by proving it is both injective and surjective.
-- 

-- BEGIN ORIGINAL BLOCK 038; source line 1366
/-- Examples about proving isomorphism between groups -/
noncomputable example {G : Type u1}{H : Type u2}[Group G] [Group H] (f : G →* H)(hf1 : Function.Injective f)
  (hf2 : Function.Surjective f) : G ≃* H :=
  (MulEquiv.ofBijective f ⟨hf1, hf2⟩)

-- END ORIGINAL BLOCK 038

-- 
-- ---
-- 
-- ### 3.5.2 Key Properties of Group Homomorphisms
-- 
-- Let $f : G \to H$ be a group homomorphism. Then:
-- 
-- - $f(e_G) = e_H$
-- - The image of a subgroup is a subgroup: $f(S) \leq H$ if $S \leq G$
-- 

-- BEGIN ORIGINAL BLOCK 039; source line 1383

-- Ex. 3.5.2 Properties about homomorphism between groups
theorem ex5_2_hom_1 {G H : Type*} [Group G] [Group H]
  (α : (MulEquiv G H)) : α (1) = (1) := by
  -- We just need do some calcularate
  have one_inv_g : (1:G) * (1:G)⁻¹ = (1:G) := by group
  have inv_to_inv : ∀ x :G ,  α (x⁻¹ )=(α x)⁻¹ :=by simp only [map_inv, implies_true]
  calc
   _= α (1 * 1⁻¹) := by rw [one_inv_g]
   --2. $\alpha (1)=\alpha(1 * 1^{-1})$
   _= α (1)* α (1⁻¹ ):= by simp only [inv_one, mul_one, map_one]
   --3. $\alpha(1 * 1^{-1})=\alpha(1)* \alpha (1^{-1})$
   _= α (1)*α (1)⁻¹ := by rw[inv_to_inv]
   --4. $\alpha(1 )*\alpha( 1^{-1})=\alpha(1)* \alpha^{-1} (1)=1 $
   _=1 := by simp only [map_one, inv_one, mul_one]


-- Ex. 3.5.2 If $f: G \rightarrow H$ is a homomorphism and is any subgroup of $G$, then $f(K)=\{f(x): x \in K\}$ is a subgroup of H.
def image {G H : Type*}[Group G][Group H](K : Subgroup G)(f : G →* H) :Set H := {a : H | ∃ t ∈ K , f t= a}
example {G H : Type*}[Group G][Group H](K : Subgroup G)(f : G →* H) : Subgroup H where
  -- We need to prove that the image of a homomorphism is a subgroup of $H$.
  carrier := image K f
  mul_mem' := by
    --suppose that $a, b \in f(G)$ which means there exists $t,k\in K$ s.t. $f(t)=a, f(k)=b$. Then $ab = f(tk)$ by simple calculations using properties of homomorphism, which means $ab$ in the image of $f$ applying the fact $tk \in K$.
    intro a b ha hb
    unfold image at ha hb
    simp only [Set.mem_setOf_eq] at ha hb
    rcases ha with ⟨t , ht, hht⟩
    rcases hb with ⟨k , hk, hhk⟩
    unfold image
    simp only [Set.mem_setOf_eq]
    use t * k
    constructor
    · exact (Subgroup.mul_mem_cancel_right K hk).mpr ht
    · calc
        _ = f t * f k := by rw [@MonoidHom.map_mul]
        _ = _ := by simp [hht, hhk]
  one_mem' := by
    unfold image
    use 1
    constructor
    · exact Subgroup.one_mem K
    · exact MonoidHom.map_one f
  inv_mem' := by
    --Suppose that $x = f(t)$ is element of image, $t\in K$, then $x^{-1}=f(t^{-1})$ and $t^{-1}\in K$ provide $x^{-1} \in \text{image}$.
    rintro x hx
    rcases hx with ⟨t, tink, ht⟩
    use t⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff K).mpr tink
    · calc
        _ = f t⁻¹ * 1 := by simp
        _ = f t⁻¹ * (f t * (f t)⁻¹) := by rw [@mul_inv_cancel]
        _ = f t⁻¹ * f t * (f t)⁻¹ := by rw [@Semigroup.mul_assoc]
        _ = f (t⁻¹ * t) * (f t)⁻¹:= by rw [@MonoidHom.map_mul]
        _ = f (1) * (f t)⁻¹ :=by rw [@inv_mul_cancel]
        _ = 1 * (f t)⁻¹ := by rw [@MonoidHom.map_one]
        _ = (f t)⁻¹ := by rw [one_mul]
        _ = _ := by rw [ht]

-- END ORIGINAL BLOCK 039

-- ---
-- 
-- ### 3.5.3 First Isomorphism Theorem
-- 
-- Let $f : G \to H$ be a group homomorphism. Then:
-- 
-- The quotient group $G / \ker(f)$ is isomorphic to $\mathrm{im}(f)$:
-- $$
-- G / \ker(f) \cong \mathrm{im}(f)
-- $$
-- 
-- This theorem is central in group theory and allows one to "factor" a group through a homomorphism.
-- 

-- BEGIN ORIGINAL BLOCK 040; source line 1459
-- Ex. 3.5.3 If $f : G \rightarrow G^{\prime}$ is a homomorphism of groups, then $f$ induces an isomorphism $G / \operatorname{Ker}f  \cong \operatorname{Im} f$
noncomputable example {G G' : Type*} [Group G] [Group G'] {f : G →* G'} : G ⧸ f.ker ≃* f.range := by
  -- This is exactly the first isomorphism theorem.
  exact QuotientGroup.quotientKerEquivRange f
-- END ORIGINAL BLOCK 040

-- ---
-- 
-- ### 3.5.4 Examples about Group Homomorphism
-- 
-- #### Ex1. If $f$ is an automorphism of $\mathbb{Z}$, and $I$ is the identity function on $\mathbb{Z}$, show that $f$ is either $I$ or $-I$.
-- 

-- BEGIN ORIGINAL BLOCK 041; source line 1471
/--We define the isomorphism $-1$ on $\mathbb{Z}$.-/
def neg_i : ℤ≃+ ℤ where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := fun x => by simp
  right_inv := fun x => by simp
  map_add' := by
    intro x y
    ring
/--All the automorphisms of $\mathbb{Z}$ are either the identity or the negation.-/
theorem iso_eq_id (f : ℤ≃+ ℤ) : f = neg_i ∨ f = 1 := by
--First we show that $f(n)=n*f(1)$ for all $n$ and we use induction on $n$ to solve the case when $n$ is a natural number.
  have h1 (a : ℕ) : (f a) = a * (f 1) := by
    induction' a with n hn
    · simp only [CharP.cast_eq_zero, map_zero, zero_mul]
    · rw [Int.natCast_add]
      rw [map_add,hn]
      ring_nf
--Then for the negative case, we can use the fact that $f(-n)=-f(n)$ and the positive case is the same as the case when $n$ is a natural number.
  have h2 (a : ℤ) : (f a) = a * (f 1) := by
    if h : a ≥ 0 then
      have hn : ∃ (n : ℕ), a = n := by
        exact Int.eq_ofNat_of_zero_le h
      rcases hn with ⟨n,hn⟩
      rw [hn]
      exact h1 n
    else
      have hn : ∃ (n : ℕ), a = -n := by
        refine Int.exists_eq_neg_ofNat ?H
        linarith
      rcases hn with ⟨n,hn⟩
      rw [hn]
      rw [map_neg,h1 n]
      simp only [neg_mul]
--Then using the surjectivity of $f$, we can choose $a$ such that $f(a)=1$.
  have hf : Function.Surjective f := by
    exact AddEquiv.surjective f
--We prove that $f(1)=1$ or $f(1)=-1$.
  have h3 : f 1 = 1 ∨ f 1 = -1 := by
    have t1 : ∃ (a : ℤ), f a = 1 := by
      exact hf 1
    rcases t1 with ⟨a,ha⟩
    rw [h2 a] at ha
--Thus we have $a*f(1)=1$.
    have ha0 : (f 1) ≠ 0 := by
      intro h
      rw [h] at ha
      simp only [mul_zero, zero_ne_one] at ha
--Combining with the fact that $a,f(1)$ are integers, we have $f(1)=1$ or $f(1)=-1$.
    have h0 : a ≠ 0 := by
      intro h
      rw [h] at ha
      simp only [zero_mul] at ha
      tauto
    have ha2 : |a|≥ 1 := by
      exact Int.one_le_abs h0
    have tt : |1| = |a| * |f 1| := by
      nth_rw 1 [← ha]
      exact abs_mul a (f 1)
    simp only [abs_one] at tt
    have tt1 : 1 ≥ |f 1| := by
      nth_rw 1 [tt]
      have : |a| * |f 1| ≥ 1 * |f 1| := by
        refine Int.mul_le_mul_of_nonneg_right ha2 ?h₂
        exact abs_nonneg (f 1)
      rw [one_mul] at this
      exact this
    have : |f 1| ≤ 1 := tt1
    rw [Int.abs_le_one_iff] at this
    tauto
  rcases h3 with h3 | h3
--If $f(1)=1$, then $f$ is the identity using the fact that $f(n)=n*f(1)$.
  · right
    apply AddEquiv.ext
    intro x
    rw [h2 x,h3]
    simp only [mul_one, AddAut.one_apply]
--If $f(1)=-1$, then $f$ is the negation the same way as the positive case.
  · left
    apply AddEquiv.ext
    intro x
    rw [h2 x,h3]
    simp only [Int.reduceNeg, mul_neg, mul_one]
    exact rfl

-- END ORIGINAL BLOCK 041

-- 
-- #### Ex2. Let $F$ be a field of characteristic zero and let $D$ be the formal polynomial differentiation map, so that $$ D\left(a_{0}+a_{1} x+a_{2} x^{2}+\cdots+a_{n} x^{n}\right)=a_{1}+2 \cdot a_{2} x+\cdots+n \cdot a_{n} x^{n-1} . $$ a. Show that $D: F[x] \rightarrow F[x]$ is a group homomorphism of $\langle F[x],+\rangle$ into itself. Is $D$ a ring homomorphism?
-- 

-- BEGIN ORIGINAL BLOCK 042; source line 1560
/-- 27. Let $F$ be a field of characteristic zero and let $D$ be the formal polynomial differentiation map, so that $$ D\left(a_{0}+a_{1} x+a_{2} x^{2}+\cdots+a_{n} x^{n}\right)=a_{1}+2 \cdot a_{2} x+\cdots+n \cdot a_{n} x^{n-1} . $$ a. Show that $D: F[x] \rightarrow F[x]$ is a group homomorphism of $\langle F[x],+\rangle$ into itself. Is $D$ a ring homomorphism?-/
noncomputable def D {R : Type u} [Field R] : R[X] →+ R[X] := {
  derivative with
  map_zero' := Polynomial.derivative_zero
  }
/-- simp lemma for `D`. -/
@[simp]
lemma D_eq {R : Type u} [Field R](f : R[X]) : D f = derivative f := rfl
/-- Show that `D` is not a ring homorphism. -/
theorem derivative_not_ring_hom {R : Type u} [Field R][CharZero R] : ¬ (∃ f : R[X] →+* R[X], f.toAddMonoidHom = D) := by
  intro ⟨f, hf⟩ -- assume f is a ring homomorphism and f.toAddMonoidHom = D
  absurd f.map_mul -- Then we prove that contradicts to the the `map_mul`.
  push_neg
  use X, (X + 1)
  -- We will show that `f` does not preserve multiplication by show that `f (X * (X + 1)) ≠ f X * f (X + 1)`
  show f.toAddMonoidHom (X * (X + 1)) ≠ f.toAddMonoidHom X * f.toAddMonoidHom (X + 1)
  rw [hf]
  simp only [D_eq, derivative_mul, derivative_X, one_mul, derivative_add, derivative_one, add_zero,
    mul_one, ne_eq]
  -- By simplifying the above expression, we need to show `X + 1 + X ≠ 1 `
  intro h -- Assume `X + 1 + X = 1`
  apply_fun (Polynomial.eval 1) at h -- Evaluate the above expression at 1
  simp only [eval_add, eval_X, eval_one, add_eq_right, add_self_eq_zero, one_ne_zero] at h
  -- Then we get `2 = 1` which is a contradiction to `CharZero R` .

-- END ORIGINAL BLOCK 042

-- 
-- ---
-- 
-- 
-- ## 3.6 Famous Group Examples
-- 
-- ### 3.6.1 Permuation Group
-- 
-- A **permutation group** is a group whose elements are bijective functions (permutations) from a set to itself, and whose group operation is the composition of such functions.
-- 
-- Given a finite type `α`, the group of permutations on `α` is denoted by `Equiv.Perm α` in Lean. This is the group of all bijective maps from `α` to itself under composition.
-- 
-- A common type used with `Equiv.Perm` is `Fin n`, where `n` is a natural number. Before introducing permutation groups in detail, we will first lay the groundwork by reviewing some basic concepts about permutations and cycles.
-- 
-- We begin by demonstrating how to represent or compute a specific permutation. Generally, there are three common approaches:
-- 
-- 1. **Directly constructing the permutation by explicitly defining its mapping.**
-- 
--     In this approach, we need to explicitly provide both the permutation function and its inverse function.

-- BEGIN ORIGINAL BLOCK 043; source line 1606
    -- Ex. Directly constructing the permutation by explicitly defining its mapping.
    def toFun₀ : Fin 8 → Fin 8
      | 0 => 0
      | 1 => 1
      | 2 => 4
      | 3 => 2
      | 4 => 3
      | 5 => 5
      | 6 => 7
      | 7 => 6
    /--
    Define the function `invFun₀` which represents the inverse mapping of the given permutation.
    This is the inverse of `toFun₀`.
    -/
    def invFun₀ : Fin 8 → Fin 8
      | 0 => 0
      | 1 => 1
      | 2 => 3
      | 3 => 4
      | 4 => 2
      | 5 => 5
      | 6 => 7
      | 7 => 6
    /--
    Define `a` as a permutation on $\text{Fin } 8$ using `toFun₀` as the forward function and `invFun₀` as the inverse function.
    We need to verify that `invFun₀` is indeed the inverse of `toFun₀`.
    -/
    def a : Equiv.Perm (Fin 8) := {
      toFun := toFun₀ -- Set the forward function of the permutation to `toFun₀`.
      invFun := invFun₀ -- Set the inverse function of the permutation to `invFun₀`.
      left_inv x := by -- Prove that `invFun₀` is the left inverse of `toFun₀`, i.e., $\text{invFun₀}(\text{toFun₀}(x)) = x$ for all $x \in \text{Fin } 8$.
        fin_cases x <;> decide -- Perform case analysis on all possible values of $x \in \text{Fin } 8$. `decide` tactic is used to automatically verify the equality in each case by computation.
      right_inv x := by -- Prove that `invFun₀` is the right inverse of `toFun₀`, i.e., $\text{toFun₀}(\text{invFun₀}(x)) = x$ for all $x \in \text{Fin } 8$.
        fin_cases x <;> decide -- Perform case analysis on all possible values of $x \in \text{Fin } 8$. `decide` tactic is used to automatically verify the equality in each case by computation.
    }
    /--
    Express the permutation `a` as a product of transpositions (2-cycles).
    The claim is that $a = (\text{swap } 2 \ 3) \circ (\text{swap } 2 \ 4) \circ (\text{swap } 7 \ 6)$.
    In cycle notation, $\text{swap } i j = (i\ j)$.
    -/
    lemma factor : a = (Equiv.swap 2 3) * (Equiv.swap 2 4) * (Equiv.swap 7 6) := by
      ext x -- Use the extensionality tactic `ext x` to prove the equality of two permutations by showing that they have the same action on every element $x \in \text{Fin } 8$.
      fin_cases x <;> decide -- Perform case analysis on all possible values of $x \in \text{Fin } 8$. `decide` tactic is used to automatically verify that both sides of the equation have the same value for each case by computation.
-- END ORIGINAL BLOCK 043

-- 2. **Describing the permutation as a product of swaps (transpositions).**
-- 

-- BEGIN ORIGINAL BLOCK 044; source line 1653
    -- Ex. Define swap 1 2 and swap 0 1 in S_3
    def σ : Perm (Fin 3) := swap 1 2
    def τ : Perm (Fin 3) := swap 0 1

    example : σ ^ 2 = 1 := by
      rw [σ]
      exact support_eq_empty_iff.mp rfl
-- END ORIGINAL BLOCK 044

-- 
-- 3. **Expressing the permutation using cycles (cycle notation).**
-- 
--     A permutation can be directly represented using the notation `c[0, 1, 2]`, which emulates the standard cyclic permutation notation `(1 2 3)`. Mathlib provides the function `Cycle.formPerm` to automatically convert a cycle into a permutation `(Equiv.Perm)`.
-- 

-- BEGIN ORIGINAL BLOCK 045; source line 1667
    -- Ex. Expressing the permutation using cycles
    example : σ * τ = c[0, 2, 1] := by
      rw [σ, τ]
      decide
-- END ORIGINAL BLOCK 045

-- 
-- 4. **Verify the Group Structure.**
-- 
--     The permutation group $S_n$, i.e., the symmetric group in mathematics, naturally forms a group structure. In Lean4, we can verify its group structure in the following way. Another common example is the alternating group $A_n$, whose group structure can also be verified.
-- 

-- BEGIN ORIGINAL BLOCK 046; source line 1678
    -- Ex. Verify the Group Structure.
    -- Ex. Perm (Fin n) has a Group Structure
    instance (n : ℕ): Group (Perm (Fin n)) := by infer_instance

    -- Ex. alternatingGroup (Fin n) has a Group Structure
    instance (n : ℕ): Group (alternatingGroup (Fin n)) := by infer_instance
-- END ORIGINAL BLOCK 046

-- 
-- 5. **Examples about Permuation Group**
-- 
--     #### Ex 1. If $f \in S_{n}$, show that $f=h_{1} h_{2} \cdots h_{m}$ for some $h_{j} \in S_{n}$ such that $h_{j}^{2}=id$.

-- BEGIN ORIGINAL BLOCK 047; source line 1690
    /--In order to prove that every permutation is a product of some swaps, we use the list of swaps obtained from the theorem Equiv.Perm.truncSwapFactors. -/
    example {n : ℕ} (f : Equiv.Perm (Fin n)) :
    ∃ l : List (Equiv.Perm (Fin n)) , l.prod = f ∧ ∀ g ∈ l, IsSwap g := by
      obtain ⟨h1, h2⟩ := Subtype.mem (truncSwapFactors f).out
      use (f.truncSwapFactors.out)

-- END ORIGINAL BLOCK 047

--     #### Ex 2. Prove that every even permutation is a product of one or more cycles of length 3. [Hint: $(13)(12)=$ $(123) ;(12)(34)=(321)(134)$.]

-- BEGIN ORIGINAL BLOCK 048; source line 1699
    /-- 3 Prove that every even permutation is a product of one or more cycles of length 3. [Hint: $(13)(12)=$ $(123) ;(12)(34)=(321)(134)$.]  -/
    theorem even_perm_is_product_of_cycles {n : ℕ} (σ : Perm (Fin n))
        (heven : σ.sign = 1) :
        ∃ l : List (Perm (Fin n)), (∀ x ∈ l, x.IsThreeCycle) ∧ σ = l.prod := by
      -- **Step 1**:  Using the equivalence between the alternating group and the subgroup
      -- generated by 3‑cycles we place $\sigma$ inside this subgroup.
      have sigmain : σ ∈ Subgroup.closure {x | x.IsThreeCycle} := by
        --  $\sigma\in A_n$ because `heven : σ.sign = 1`.  By the library lemma
        -- `Perm.closure_three_cycles_eq_alternating` this coincides with the closure
        -- of the set of 3‑cycles, giving the desired membership.
        rw [Perm.closure_three_cycles_eq_alternating]
        exact heven
      -- **Step 2**:  Define the induction predicate that will be used with
      -- `Subgroup.closure_induction`.  The predicate asserts that an element
      -- lying in the subgroup generated by 3‑cycles admits a decomposition
      -- into a list of 3‑cycles.
      let p : (g : (Perm (Fin n))) →
              g ∈ Subgroup.closure {x | x.IsThreeCycle} → Prop := by
        intro g hg
        --  $\exists l, (\forall x\in l,\, x\text{ is a 3‑cycle}) \land g = \prod l$.
        exact ∃ l : List (Perm (Fin n)),
              (∀ x ∈ l, x.IsThreeCycle) ∧ g = l.prod
      -- **Step 3**:  Prove the predicate for our concrete permutation `σ`
      -- by structural induction over the closure.
      have ind : p σ sigmain := by
        -- We use `Subgroup.closure_induction`.
        apply Subgroup.closure_induction
        · -- *Generator case*: the element is itself a 3‑cycle.
          intro g hg
          -- We take the singleton list `[g]`.
          use [g]
          constructor
          · --  Every element of `[g]` is `g`, hence is a 3‑cycle by `hg`.
            simp only [List.mem_singleton, forall_eq]
            exact hg
          · --  The product of a singleton list is the element itself.
            exact rfl
        · -- *Identity case*: the identity permutation is the empty product.
          use []
          simp only [List.not_mem_nil, IsEmpty.forall_iff,
            implies_true, List.prod_nil, and_self]
        · -- *Multiplicative closure*: products of two elements that satisfy the
          -- predicate also satisfy it.
          intro g1 g2 hg1 hg2 pg1 pg2
          rcases pg1 with ⟨l1, hl1, rfl⟩
          rcases pg2 with ⟨l2, hl2, rfl⟩
          --  Concatenate the two lists.
          use l1 ++ l2
          simp only [List.mem_append, List.prod_append, and_true]
          intro g gin
          -- Decide in which half of the concatenation `g` lies.
          rcases gin with gin1 | gin2
          exact hl1 g gin1
          exact hl2 g gin2
        · -- *Inverse closure*: inverses of elements that satisfy the predicate
          -- also satisfy it.
          intro g hg pg
          rcases pg with ⟨l, hl, rfl⟩
          --  The list of inverses, read backwards, has product `g⁻¹`.
          use (List.map (fun x => x⁻¹) l).reverse
          simp only [List.mem_reverse, List.mem_map, inv_involutive,
            Function.Involutive.exists_mem_and_apply_eq_iff,
            List.prod_inv_reverse, and_true]
          intro h hinvin
          --  A permutation is a 3‑cycle iff its inverse is.
          exact Perm.IsThreeCycle.inv_iff.mp (hl h⁻¹ hinvin)
      -- **Step 4**:  Extract the required decomposition for `σ`.
      exact ind
-- END ORIGINAL BLOCK 048

-- ### 3.6.2 Dihedral Group
-- 
-- A dihedral group is a group whose elements represent the symmetries of a regular polygon, including both rotations and reflections. These groups are fundamental examples in group theory and geometric algebra.
-- 
-- Given a natural number `n ≥ 3`, the dihedral group of order `2n` is denoted by `DihedralGroup n` in Lean. This group consists of all rigid transformations that map a regular n-gon onto itself, with the group operation being composition of transformations.
-- 
-- A typical realization uses two generators: a rotation `r` by `2π/n` radians and a reflection `s` across a fixed axis. Before exploring dihedral groups in depth, we will first establish foundational concepts about geometric transformations and generator relations.
-- 
-- We begin by showing how to represent or compute specific group elements.
-- 
-- 1. **Directly compute specific group elements.**
-- 

-- BEGIN ORIGINAL BLOCK 049; source line 1781
-- Ex. Examples about DihedralGroup
example (n : ℕ)(x : DihedralGroup n) : r 1 = x := by
  sorry

-- Ex. Examples about DihedralGroup
example (n : ℕ)(m : DihedralGroup n) : sr 2 = m := by
  sorry

-- Ex. Examples about calculation about DihedralGroup
example (n : ℕ)(i j : ZMod n) : r i * sr j * (sr i * sr j) = sr (j - i) * r (j - i) := by
  simp

-- END ORIGINAL BLOCK 049

-- 
-- 2. **Verify the Group Structure.**
-- 

-- BEGIN ORIGINAL BLOCK 050; source line 1798

-- Ex. Verify the Group Structure.
-- Ex. DihedralGroup n has a Group Structure
instance (n : ℕ): Group (DihedralGroup n) := by infer_instance

-- END ORIGINAL BLOCK 050

-- 
-- 3. **Examples about Dihedral Group**
-- 
--     #### Ex 1. Let $n$ be an integer with $n \geq 3$. (a) If $n$ is even, show that the center of $D_{n}$ is not trivial. Then find all of the elements in $Z\left(D_{n}\right)$.

-- BEGIN ORIGINAL BLOCK 051; source line 1809
    /--Let $n$ be an integer with $n \geq 3$. If $n$ is even, show that the center of $D_{n}$ is not trivial.
    Then find all of the elements in $Z\left(D_{n}\right)$.-/
    theorem center_nontrivial {n : ℕ} (eve : Even n) (ge: n≥3):(Subgroup.center (DihedralGroup n):Set (DihedralGroup n))={1,(r 1)^(n/2)} :=by
      --Show that $n≠0$
      have ne: NeZero n :=NeZero.of_gt ge
      --$n$ is even, so $\exists s\in\mathbb{N}, n=2s$.
      obtain⟨s,hs⟩:=eve;rw[←two_mul] at hs;
      ext (i|j) <;> constructor <;> intro h
      repeat' simp only [SetLike.mem_coe] at h; rw [@Subgroup.mem_center_iff] at h
      · --Show that if $r^i\in Z(D_{2n})$ then $r^i\in\{1,r^{\frac{n}{2}}\}$.
        --$r^is=sr^i$ implies $\bar{2i}=0$ i.e $n\mid 2i$, hence, $s\mid i, \exists t\in\mathbb{N}, i=t*s$.
        have eq1:=h (sr 0); simp only [sr_mul_r, zero_add, r_mul_sr, zero_sub, sr.injEq] at eq1
        rw [@eq_neg_iff_add_eq_zero] at eq1; simp only [r_one_pow, Set.mem_insert_iff,
        Set.mem_singleton_iff, r.injEq]; rw[←ZMod.natCast_zmod_val i] at eq1 ⊢
        rw [←Nat.cast_add,ZMod.natCast_eq_zero_iff,←two_mul] at eq1;
        nth_rw 1[hs] at eq1; rw [(Nat.mul_dvd_mul_iff_left (Nat.zero_lt_two))] at eq1;
        obtain⟨t,ht⟩:=eq1;
        --Show that $t\le 2$.
        have tle: t≤2 :=by
          have ge : 1≤s :=by
            by_contra! le; simp only [Nat.lt_one_iff] at le
            simp only [le, mul_zero] at hs; rw[hs] at ne; simp only [neZero_zero_iff_false] at ne
          suffices le: i.val ≤ n from by
            rw[ht,hs,mul_comm] at le; exact Nat.le_of_mul_le_mul_right le ge
          exact ZMod.val_le i
        --Since $t\le 2$, $t=0$ ,$t=1$ or $t=2$.
        simp only [Nat.le_succ_iff_eq_or_le, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add,
          nonpos_iff_eq_zero] at tle; rcases tle with L|L|L
        · --$t=2$, then $i=n$, $r i=1$.
          rw[ht,L,mul_comm,←hs]; simp only [CharP.cast_eq_zero]; exact Or.symm (Or.inr rfl)
        · --$t=1$, then $i=\frac{n}{2}$, $r^i=r^\frac{n}{2}$.
          simp only [ht, L, mul_one,hs]; apply Or.inr; simp only [ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, mul_div_cancel_left₀]
        · --$t=0$, then $r^i=r^0=1$.
          simp only [ht, L, mul_zero, Nat.cast_zero]; exact Or.symm (Or.inr rfl)
      · --Show that $\{1,r^{\frac{n}{2}}\}\subseteq Z(D_{2n})$.
        rcases h with L|L <;> simp only [SetLike.mem_coe] <;> rw[L]
        · exact Subgroup.one_mem (Subgroup.center (DihedralGroup n))
        · rw [@Subgroup.mem_center_iff]; rintro (k|l)
          · simp only [r_one_pow, r_mul_r, r.injEq]; ring_nf
          · simp only [r_one_pow, sr_mul_r, r_mul_sr, sr.injEq]; refine eq_sub_iff_add_eq'.mp ?_
            ring_nf; rw [@eq_neg_iff_add_eq_zero,←Nat.cast_add,hs]; simp only [ne_eq,
              OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
            rw[←two_mul,←hs]; exact ZMod.natCast_self n
      · /-Show that $¬sr^j\in Z(D_{2n})$ for all $j$, if $sr^j\in Z(D_{2n})$, then $sr^jr=rsr^j$,
        this implies $\bar{j-1}=\bar{j+1}$ i.e. $\bar{-1}=\bar{1}$.-/
        have ctr:=h (r 1); simp only [r_mul_sr, sr_mul_r, sr.injEq] at ctr
        rw [← @sub_eq_iff_eq_add'] at ctr; ring_nf at ctr; rw [@ZMod.neg_eq_self_iff] at ctr
        have rpl:=ZMod.val_one'' (Ne.symm (Nat.ne_of_lt (Nat.lt_of_succ_lt ge)));
        --$\bar{1}=\bar{-1}$ implies $\bar{1}=\bar{0}$ or $n=2$.
        rcases ctr with L|L
        · --$\bar{1}=\bar{0}$ implying $n\le 1$ which contradicts with $n\ge 3$.
          rw[←ZMod.natCast_zmod_val 1] at L; rw [ZMod.natCast_eq_zero_iff] at L;
          rw[rpl] at L; apply Nat.le_of_dvd Nat.one_pos at L; linarith
        · --$n=2$ contradicts with $n\ge 3$.
          simp only [rpl, mul_one] at L; linarith
      · --$¬sr^j\in \{1,r^{\frac{n}{2}}\}$.
        simp only [r_one_pow, Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, or_false] at h
        contradiction

-- END ORIGINAL BLOCK 051

-- 
--     #### Ex 2. Let $n$ be an integer with $n \geq 3$. (b) If $n$ is odd, find all elements in $Z\left(D_{n}\right)$.

-- BEGIN ORIGINAL BLOCK 052; source line 1873
    /--Wen n is odd, if the addition of a is 0, then a is 0.-/
    lemma ZMOD_add_eq_zero (n : ℕ) (od : Odd n) (ge: n≥3) (a : ZMod n) (eq1 : a + a = 0) : a = 0 := by
      --n is not zero.
      have ne: NeZero n :=NeZero.of_gt ge
      --$a+a=0$ implies $2a=0$, then $n\mid 2a$.
      rw[←ZMod.natCast_zmod_val a] at eq1 ⊢
      rw [←Nat.cast_add,ZMod.natCast_eq_zero_iff,←two_mul] at eq1
      --$n$ is odd, so $n\mid 2a$ implies $n\mid a$.
      rw [← @Nat.dvd_gcd_mul_iff_dvd_mul,Nat.coprime_two_right.mpr od,Nat.one_mul] at eq1
      --a.val is zero or a.val is a multiple of n.
      have eq3: n ≤ a.val ∨ a.val = 0 :=by
        if h: a.val = 0 then
          tauto
        else
          left
          refine @Nat.le_of_dvd n a.val ?_ eq1
          exact Nat.zero_lt_of_ne_zero h
      --We consider the two cases.
      rcases eq3 with L|L
      · contrapose! L
        exact ZMod.val_lt a
      · rw [L];simp only [Nat.cast_zero]
    /--The center of the dihedral group is trivial if n is odd and n≥3.-/
    theorem center_trivial {n : ℕ} (od : Odd n) (ge: n≥3): Subgroup.center (DihedralGroup n)=⊥ :=by
      rw [@Subgroup.eq_bot_iff_forall]
      intro x hx;rw [@Subgroup.mem_center_iff] at hx
      --It suffices to show that any element x is in the center is 1.
      rcases x with a|b
      · rw [@DihedralGroup.one_def]
        --When x is r a, x is commutative with sr 0.
        have hx1 := hx (sr 0)
        simp only [sr_mul_r, zero_add, r_mul_sr, zero_sub, sr.injEq] at hx1
        rw [@eq_neg_iff_add_eq_zero] at hx1
        rw [← ZMOD_add_eq_zero n od ge a hx1]
        --When x is sr b, we have that x is commutative with r b.
      · have hx1 := hx (r b)
        simp only [r_mul_sr, sub_self, sr_mul_r, sr.injEq] at hx1
        contrapose! hx
        rw [(ZMOD_add_eq_zero n od ge b hx1.symm)]
        use r 1;simp only [r_mul_sr, zero_sub, sr_mul_r, zero_add, ne_eq, sr.injEq]
        rw [← @Ne.eq_def]
        refine @ZMod.neg_one_ne_one n ?_
        exact { out := ge }

-- END ORIGINAL BLOCK 052


end OriginalLecture
