/-!
# Tiny Lean Proofs

Examples of the smallest possible proofs in Lean 4.  Each lemma is chosen so
that the kernel can validate it with a single primitive rule such as `rfl`
(reflexivity), direct projection, or immediate constructor introduction.
-/

-- Enable trace output to see kernel-level type checking
set_option trace.Elab.definition.body true   -- Show the elaborated proof term
set_option trace.compiler.ir.result true     -- Show intermediate representation
set_option pp.explicit true                  -- Show all implicit arguments
set_option pp.proofs true                    -- Show proof terms (don't replace with _)
set_option pp.all true                       -- Show everything in full detail

-- We'll also add #check commands to show how the kernel validates each step

theorem true_is_true : True :=
  True.intro

#print true_is_true

theorem assume_prop_is_true (P : Prop) (h : P) : P :=
  h

theorem assume_prop_is_true2 : ∀ (P : Prop) (_ : P), P :=
  fun (P : Prop) (h : P) =>  h

theorem assume_prop_is_true3 : ∀ (P : Prop), P → P :=
  fun (P : Prop) (h : P) =>  h

theorem modus_ponens (P Q : Prop) (hp : P) (f : P → Q) : Q :=
  f hp

def modus_ponens3 : ∀ (P Q : Prop), P → (P → Q) → Q :=
  fun (A B : Prop) (evidence : A) (implication : A → B) => implication evidence  

#check modus_ponens

/-- Reflexivity (`rfl`) is the simplest proof: any term is definitionally equal to itself. -/
theorem refl_example (α : Sort _) (x : α) : x = x :=
  rfl

/-- Identity functions can be proven with a single lambda that hands the input back. -/
theorem id_preserves (P : Prop) : P → P :=
  fun h => h

/-- Conjunction projections reduce to retrieving `.left` or `.right` from the proof pair. -/
theorem and_right {P Q : Prop} : P ∧ Q → Q :=
  fun h => h.right

/-- Numerals are definitionally equal to themselves; no arithmetic reasoning is needed. -/
theorem zero_eq_zero : (0 : Nat) = 0 :=
  rfl

/-- `Eq.refl` can be chained by function application; the kernel does not need rewriting here. -/
theorem apply_id {α : Sort _} (x : α) : (fun y => y) x = x :=
  rfl
