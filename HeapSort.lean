
inductive Tree where
| Nil
| Node (val : Int) (n1: Tree) (n2 : Tree) : Tree


def insert : Int -> Tree -> Tree
| x, Tree.Nil  => Tree.Node x Tree.Nil Tree.Nil
| x, (Tree.Node a left right) => if x ≤ a then Tree.Node a ( insert x left ) right else Tree.Node a left ( insert x right )

def heapify : List Int -> Tree
| []  => Tree.Nil
| (x :: xs) => insert x ( heapify xs )

def tree2list : Tree -> List Int
| Tree.Nil  => []
| (Tree.Node a left right) => tree2list left ++ [a] ++ tree2list right


def heapSort i := tree2list (heapify i)


#eval heapSort [5,2,8,1,3,7,9]

#eval heapSort [9,7,3,1,8,2,5]

def heap1 := heapSort [5,2,9,3,1,7,0,6]


-----------------------------------------
-- isElem
-----------------------------------------

def isElem : Int -> List Int -> Prop
| _, [] => False
| a, b :: bs => if a = b then True else isElem a bs


def isElemTree : Int -> Tree -> Prop
| _ , Tree.Nil => False
| a, (Tree.Node b right left) => if a = b then True else isElemTree a right ∨ isElemTree a left


theorem isElemTree_singleton : ∀ (x z : Int), isElemTree z (Tree.Node x Tree.Nil Tree.Nil) → z = x := by simp [isElemTree]



theorem isElemTree_branch : ∀ (a b : Int), ∀  (tl tr : Tree), isElemTree a (Tree.Node b tl tr) → (a = b ∨ isElemTree a tl ∨ isElemTree a tr) := by
  intros a b tl tr h
  if h_ab : a = b then
    exact Or.inl h_ab
  else
    rw [isElemTree] at h
    rw [if_neg h_ab] at h
    exact Or.inr h




theorem isElemTree_node_insert_left : ∀ (x a y : Int), ∀ (tl tr : Tree), isElemTree x (Tree.Node a (insert y tl) tr ) → x = a ∨ isElemTree x (insert y tl) ∨ isElemTree x tr := by
  intros x a y tl tr h
  simp! at h
  if x_eq_a : x = a then
    exact Or.inl x_eq_a
  else
    have h2 := h x_eq_a
    exact Or.inr h2





------------------------------
-- Verification of HeapSort
------------------------------

-- Predicate: Sorted
def sorted : List Int -> Prop
| [] => True
| [_] => True
| (x :: y :: xs) => x ≤ y ∧ sorted (y :: xs)


def heap : Tree -> Prop
| Tree.Nil => True
| Tree.Node a left right =>
  heap left ∧ heap right ∧
  (∀ (x : Int), isElemTree x left → a ≥ x) ∧
  (∀ (x : Int), isElemTree x right → a ≤  x)

theorem heap_empty : heap Tree.Nil := True.intro

theorem heap_singleton : ∀ (x : Int), heap (Tree.Node x Tree.Nil Tree.Nil) := by
  simp!


-- if x ≤ y then Tree.Node y (Tree.Node x Tree.Nil Tree.Nil) Tree.Nil is a heap
theorem heap_double : ∀ (x y : Int), ∀ (_ : x ≤ y), heap (Tree.Node y (Tree.Node x Tree.Nil Tree.Nil) Tree.Nil) := by
  intros x y h_le
  simp!
  exact h_le







-- ------------------------------
-- -- prove that HeapSort sorts
-- ------------------------------

-- inserting into an empty Tree gives you a singleton
def tree_insert_nil : ∀ (x : Int), insert x Tree.Nil = Tree.Node x Tree.Nil Tree.Nil := by simp [_root_.insert]

-- insert x Tree.Nil is a heap
theorem heap_insert_nil : ∀ (x : Int), heap (insert x Tree.Nil) := by
  intros x
  simp!


-- insert x (Tree.Node a Tree.Nil Tree.Nil) is a heap
-- idk how to condense it yet
theorem heap_insert_singleton: ∀ (x y: Int), heap (insert x (Tree.Node y Tree.Nil Tree.Nil)) := by
  intro x y
  if x_le_y : x ≤ y then
    repeat rw [_root_.insert]
    rw [if_pos x_le_y]
    exact heap_double x y x_le_y
  else
    rw [_root_.insert]
    rw [if_neg x_le_y]
    have y_le_x : y ≤ x := Int.le_of_lt (Int.lt_of_not_ge x_le_y)
    rw [_root_.insert]
    constructor
    .
      exact heap_empty
    .
      constructor
      .
        exact heap_singleton x
      .
        constructor
        .
          intros z h
          contradiction
        .
          intros z h
          simp [isElemTree] at h
          rw [h]
          exact y_le_x







theorem isElemTree_branch_insert : ∀ (x y : Int), ∀ (tl : Tree), isElemTree x tl → isElemTree x (insert y tl) := by
  intros x y tl h_xtl
  induction tl with
  | Nil =>
    contradiction
  | Node a tl tr h_tl h_tr =>
    rw [_root_.insert]
    if y_le_a : y ≤ a then
      rw [if_pos y_le_a]
      have h := isElemTree_branch x a tl tr h_xtl
      cases h with
      | inl x_eq_a =>
        rw [isElemTree]
        rw [if_pos x_eq_a]
        exact True.intro
      | inr tl_or_tr =>
        cases tl_or_tr with
        | inl x_tl =>
          have h := h_tl x_tl
          rw [isElemTree]
          if x_eq_a : x = a then
            rw [if_pos x_eq_a]
            exact True.intro
          else
            rw [if_neg x_eq_a]
            exact Or.inl h
        | inr x_tr =>
          rw [isElemTree]
          if x_eq_a : x = a then
            rw [if_pos x_eq_a]
            exact True.intro
          else
            rw [if_neg x_eq_a]
            exact Or.inr x_tr
    else
      rw [if_neg y_le_a]
      rw [isElemTree]
      have h := isElemTree_branch x a tl tr h_xtl
      cases h with
      | inl x_eq_a =>
        rw [if_pos x_eq_a]
        exact True.intro
      | inr tl_or_tr =>
        cases tl_or_tr with
        | inl x_tl =>
          if x_eq_a : x = a then
            rw [if_pos x_eq_a]
            exact True.intro
          else
            rw [if_neg x_eq_a]
            exact Or.inl x_tl

        | inr x_tr =>
          have h := h_tr x_tr
          if x_eq_a : x = a then
            rw [if_pos x_eq_a]
            exact True.intro
          else
            rw [if_neg x_eq_a]
            exact Or.inr h






theorem isElemTree_insert : ∀ (x y : Int), ∀ (t : Tree), isElemTree x (insert y t) → x = y ∨ isElemTree x t := by
  intros x y t h_t
  induction t with
  | Nil =>
    rw [_root_.insert] at h_t
    exact Or.inl (isElemTree_singleton y x h_t)
  | Node a tl tr h_tl h_tr =>
    if y_le_a : y ≤ a then
      rw [_root_.insert] at h_t
      rw [if_pos y_le_a] at h_t
      by_cases h : x = a
      case pos =>
        rw [isElemTree]
        rw [if_pos h]
        exact Or.inr True.intro
      case neg =>
        rw [isElemTree] at h_t
        rw [if_neg h] at h_t
        cases h_t with
        | inl h_xytl =>
          have h2 := h_tl h_xytl
          cases h2 with
          | inl h_xy => exact Or.inl h_xy
          | inr h_xtl =>
            rw [isElemTree]
            rw [if_neg h]
            exact Or.inr (Or.inl h_xtl)
        | inr h_xtr =>
          rw [isElemTree]
          rw [if_neg h]
          exact Or.inr (Or.inr h_xtr)
    else
      simp! at h_t
      rw [if_neg y_le_a] at h_t
      by_cases h : x = a
      case pos =>
        rw [isElemTree]
        rw [if_pos h]
        exact Or.inr True.intro
      case neg =>
        rw [isElemTree, if_neg h] at h_t
        rw [isElemTree, if_neg h]
        cases h_t with
        | inl h_xtl => exact Or.inr (Or.inl h_xtl)
        | inr h_xytr =>
          have h2 := h_tr h_xytr
          cases h2 with
          | inl h_xy => exact Or.inl h_xy
          | inr h_xtr => exact Or.inr (Or.inr h_xtr)




theorem invariant : ∀ (x : Int), ∀ (t : Tree), heap t → heap (insert x t) := by
  intros x t h
  induction t with
  | Nil => exact heap_insert_nil x
  | Node y tl tr h_tl h_tr =>
    simp!
    simp! at h
    if x_le_y : x ≤ y then
      have h2 := h_tl (And.left h)
      rw [if_pos x_le_y]
      simp!
      constructor
      .
        exact h2
      .
        constructor
        .
          exact And.left (And.right h)
        .
          constructor
          .
            intros a h_a
            have h_insert := isElemTree_insert a x tl h_a
            induction h_insert with
            | inl h_ax =>
              rw [h_ax]
              exact x_le_y
            | inr h_atl =>
              have h_xtl := (And.left (And.right (And.right h)) a) h_atl
              exact h_xtl
          .
            exact (And.right (And.right (And.right h)))

    else
      rw [if_neg x_le_y]
      constructor
      .
        exact And.left h
      .
        constructor
        .
          exact h_tr (And.left (And.right h))
        .
          constructor
          .
            exact (And.left (And.right (And.right h)))
          .
            intros a h_axtr
            have h_axtr_insert := isElemTree_insert a x tr h_axtr
            induction h_axtr_insert with
            | inl h_ax =>
              rw [h_ax ]
              have y_le_x := Int.le_of_not_le x_le_y
              exact y_le_x
            | inr h_atr =>
              have h_xtr := (And.right (And.right (And.right h))) a h_atr
              exact h_xtr
