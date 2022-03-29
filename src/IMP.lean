abbreviation vname  := string
abbreviation val    := ℕ
abbreviation pstate := vname → val

inductive aexp : Type
| N    : ℕ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

-- TODO: vedere meglio funzionamento
def aexp.toString : aexp → string
| (aexp.N n)        := "(N " ++ n.repr ++ ")"
| (aexp.V x)        := "(V " ++ x ++ ")"
| (aexp.Plus a₁ a₂) := "(Plus " ++ aexp.toString a₁ ++ " " ++ aexp.toString a₂ ++ ")"

@[instance]
def aexp.has_repr : has_repr aexp := ⟨ aexp.toString ⟩

open aexp

def aval : aexp → pstate → val
| (N n)        _ := n
| (V x)        s := s x
| (Plus a₁ a₂) s := (aval a₁ s) + (aval a₂ s)

#eval aval (Plus (N 3) (V "x")) (λ _, 0)

def substitute : aexp → aexp → vname → aexp
| (N n)        _  _ := (N n)
| (V x)        a' y := if (x = y) then a' else (V x)
| (Plus a₁ a₂) a' y := Plus (substitute a₁ a' y) (substitute a₂ a' y)

notation a `[` a' ` // ` x `]` := substitute a a' x

#eval (Plus (V "x") (N 5)) [(N 6) // "x"]

def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ y, if (y = x) then v else s y

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]` := (λ _, 0 ) [x ↦ v]

#eval ["x" ↦ 7]["y" ↦ 3] "x"

-- TODO: già esistente nella libreria?
lemma neg_eq_symm {α : Type} {a b : α} : ¬(a = b) ↔ ¬(b = a) :=
begin
  split,
  all_goals { intro h₁, intro h₂, exact h₁ (h₂.symm) }
end

lemma substitution {a a' : aexp} {x : vname} {s : pstate} : 
  aval (a[a' // x]) s = aval a (s[x ↦ aval a' s]) :=
begin
  induction a,
    case N : { reflexivity },
    case V : z { 
      cases (classical.em (x = z)),
        case or.inl : { -- x = z
          rw[substitute, state_update, aval],
          repeat { rw[if_pos h.symm] }
        },
        case or.inr : { -- x ≠ z
          rw[substitute, state_update, aval],
          repeat { rw[if_neg (neg_eq_symm.mp h)] },
          rw[aval]
        }
    },
    case Plus : a₁ a₂ ih₁ ih₂ {
      rw[substitute, aval, ih₁, ih₂, aval],
    }
end

lemma substitution_eq {a a₁ a₂ : aexp} {s : pstate} {x : vname} : 
  (aval a₁ s = aval a₂ s) →
  (aval (a[a₁ // x]) s) = (aval (a[a₂ // x]) s) :=
begin
  assume h : aval a₁ s = aval a₂ s,
  repeat { rw[substitution] },
  rw[h]
end

inductive bexp : Type
| Bc   : bool → bexp
| Not  : bexp → bexp
| And  : bexp → bexp → bexp
| Less : aexp → aexp → bexp

open bexp

def bval : bexp → pstate → bool
| (Bc v)       _ := v
| (Not b)      s := ¬(bval b s)
| (And b₁ b₂)  s := (bval b₁ s) ∧ (bval b₂ s)
| (Less a₁ a₂) s := (aval a₁ s) < (aval a₂ s)

#eval bval (And (Bc true) (Not (Bc false))) (λ _, 0)
#eval bval (And (Bc true) (Not (Less (V "y") (N 0)))) (["x" ↦ 7]["y" ↦ 3])

inductive com : Type
| SKIP   : com
| Assign : vname → aexp → com
| Seq    : com → com → com
| If     : bexp → com → com → com
| While  : bexp → com → com

infix ` ::= `:68                                    := com.Assign
infix ` ;; `:67                                     := com.Seq
notation `IF `:0 b ` THEN `:0 c₁ ` ELSE `:68 c₂:68  := com.If b c₁ c₂
notation `WHILE `:0 b ` DO `:68 c:68                := com.While b c