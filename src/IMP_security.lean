import tactic.induction
import order.min_max

abbreviation vname  := string
abbreviation val    := ℕ
abbreviation pstate := vname → val

inductive aexp : Type
| N    : ℕ → aexp
| V    : vname → aexp
| Plus : aexp → aexp → aexp

open aexp

def aval : aexp → pstate → val
| (N n)        _ := n
| (V x)        s := s x
| (Plus a₁ a₂) s := (aval a₁ s) + (aval a₂ s)

def state_update (s : pstate) (x : vname) (v : val) : pstate :=
  λ y, if (y = x) then v else s y

notation s `[` x ` ↦ ` v `]`:100 := state_update s x v
notation   `[` x ` ↦ ` v `]` := (λ _, 0 ) [x ↦ v]

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

abbreviation lv := ℕ

def sec : vname → lv :=
  λ (x : vname), x.length

def secₐ : aexp → lv
| (N n)        := 0
| (V x)        := sec x
| (Plus a₁ a₂) := max (secₐ a₁) (secₐ a₂)

def sec₆ : bexp → lv
| (Bc v)       := 0
| (Not b)      := sec₆ b
| (And b₁ b₂)  := max (sec₆ b₁) (sec₆ b₂)
| (Less a₁ a₂) := max (secₐ a₁) (secₐ a₂)

notation s ` = ` t ` ⦅<= ` l `⦆` := ∀ (z : vname), (sec z <= l) → s z = t z
notation s ` = ` t ` ⦅< ` l `⦆` := ∀ (z : vname), (sec z < l) → s z = t z

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

abbreviation conf := com × pstate

open com

inductive big_step : conf → pstate → Prop
| Skip {s : pstate} : 
  big_step (SKIP, s) s

| Assign {s : pstate} {x : vname} {a : aexp} : 
  big_step (x ::= a, s) (s[x ↦ aval a s])

| Seq {c₁ c₂ : com} {s₁ s₂ s₃ : pstate} : 
  big_step (c₁, s₁) s₂ →
  big_step (c₂, s₂) s₃ → 
  big_step (c₁ ;; c₂, s₁) s₃

| IfTrue {b : bexp} {c₁ c₂ : com} {s t : pstate}  : 
  bval b s →
  big_step (c₁, s) t → 
  big_step (IF b THEN c₁ ELSE c₂, s) t

| IfFalse {b : bexp}  {c₁ c₂ : com} {s t : pstate} :
  ¬ bval b s → 
  big_step (c₂, s) t →
  big_step (IF b THEN c₁ ELSE c₂, s) t

| WhileFalse {b : bexp} {c : com} {s : pstate} :
  ¬ bval b s →
  big_step (WHILE b DO c, s) s

| WhileTrue {b : bexp} {c : com} {s₁ s₂ s₃ : pstate } :
  bval b s₁ →
  big_step (c, s₁) s₂ →
  big_step (WHILE b DO c, s₂) s₃ →
  big_step (WHILE b DO c, s₁) s₃

infix ` ⟹ `:70 := big_step

open big_step

inductive sec_type : lv → com → Prop
| Skip {l : lv} : 
  sec_type l SKIP

| Assign {x : vname} {a : aexp} {l : lv} :
  secₐ a <= sec x →
  l <= sec x →
  sec_type l (x ::= a)

| Seq {l : lv} {c₁ c₂ : com} :
  sec_type l c₁ →
  sec_type l c₂ →
  sec_type l (c₁ ;; c₂)

| If {b : bexp} {l : lv} {c₁ c₂ : com} :
  sec_type (max (sec₆ b) l) c₁ →
  sec_type (max (sec₆ b) l) c₂ →
  sec_type l (IF b THEN c₁ ELSE c₂)

| While {b : bexp} {l : lv} {c : com} :
  sec_type (max (sec₆ b) l) c →
  sec_type l (WHILE b DO c)

infix ` ⊢ₛ `:50 := sec_type

open sec_type

theorem noninterference {c : com} {s s' t t' : pstate} {l : lv}:
  (c, s) ⟹ s' → (c, t) ⟹ t' → (0 ⊢ₛ c) → s = t ⦅<= l⦆ → s' = t' ⦅<= l⦆ :=
begin
  intros _ _ _ _,
  induction' ‹(c, s) ⟹ s'›,
    case Skip : { sorry },
    case Assign : { sorry },
    case Seq : _ _ s s₁ s' _ _ ih₁ ih₂ { -- PROBLEMATIC CASE
      cases' ‹(c₁ ;; c₂, t) ⟹ t'› with _ _ _ _ _ _ t t₁,
      cases' ‹0 ⊢ₛ c₁ ;; c₂›,

      have : s₁ = t₁ ⦅<= l⦆, from ih₁ ‹(c₁, t) ⟹ t₁› ‹0 ⊢ₛ c₁› ‹s = t ⦅<= l⦆›,
      
      show s' = t' ⦅<= l⦆, from sorry -- Here I need a more general version of ih₂
    },
    case IfTrue : { sorry },
    case IfFalse : { sorry },
    case WhileTrue : { sorry },
    case WhileFalse : { sorry } 
end