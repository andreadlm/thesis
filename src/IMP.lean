namespace IMP

abbreviation vname := string
abbreviation val   := ℕ
abbreviation state := vname → val

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

def aval : aexp → state → val
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

def state_update (s : state) (x : vname) (v : val) : state :=
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

lemma substitution {a a' : aexp} {x : vname} {s : state} : 
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

lemma substitution_eq {a a₁ a₂ : aexp} {s : state} {x : vname} : 
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

def bval : bexp → state → bool
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

infix ` ::= `:68                                     := com.Assign
infix ` ;; `:67                                     := com.Seq
notation `IF `:0 b ` THEN `:0 c₁ ` ELSE `:68 c₂:68  := com.If b c₁ c₂
notation `WHILE `:0 b ` DO `:68 c:68                := com.While b c

open com

inductive big_step : com × state → state → Prop
| Skip {s : state} : 
  big_step (SKIP, s) s

| Assign {s : state} {x : vname} {a : aexp} : 
  big_step (x ::= a, s) (s[x ↦ aval a s])

| Seq {c₁ c₂ : com} {s₁ s₂ s₃ : state} : 
  big_step (c₁, s₁) s₂ →
  big_step (c₂, s₂) s₃ → 
  big_step (c₁ ;; c₂, s₁) s₃

| IfTrue {b : bexp} {c₁ c₂ : com} {s t : state}  : 
  bval b s →
  big_step (c₁, s) t → 
  big_step (IF b THEN c₁ ELSE c₂, s) t

| IfFalse {b : bexp}  {c₁ c₂ : com} {s t : state} :
  ¬ bval b s → 
  big_step (c₂, s) t →
  big_step (IF b THEN c₁ ELSE c₂, s) t

| WhileFalse {b : bexp} {c : com} {s : state} :
  ¬ bval b s →
  big_step (WHILE b DO c, s) s

| WhileTrue {b : bexp} {c : com} {s₁ s₂ s₃ : state } :
  bval b s₁ →
  big_step (c, s₁) s₂ →
  big_step (WHILE b DO c, s₂) s₃ →
  big_step (WHILE b DO c, s₁) s₃

infix ` ⇒ `:70 := big_step

open big_step

namespace big_step

namespace rule_inversion

lemma skip {s t : state} (h : (SKIP, s) ⇒ t) : 
  t = s :=
begin cases ‹(SKIP, s) ⇒ t›, reflexivity end

lemma assign {x : vname} {a : aexp} {s t : state} (h : (x ::= a, s) ⇒ t) : 
  t = (s[x ↦ aval a s]) :=
begin cases ‹(x ::= a, s) ⇒ t›, reflexivity end 

lemma seq {c₁ c₂ : com} {s₁ s₃ : state} (h : (c₁ ;; c₂, s₁) ⇒ s₃) : 
  ∃ (s₂ : state), (c₁, s₁) ⇒ s₂ ∧ (c₂, s₂) ⇒ s₃ :=
begin
  cases ‹(c₁ ;; c₂, s₁) ⇒ s₃›,
  apply exists.intro,
  split,
    exact ‹(c₁, s₁) ⇒ h_s₂›,
    exact ‹(c₂, h_s₂) ⇒ s₃›
end

lemma ifte {b : bexp} {c₁ c₂ : com} {s t : state} (h : (IF b THEN c₁ ELSE c₂, s) ⇒ t) :
  (bval b s ∧ (c₁, s) ⇒ t) ∨ (¬bval b s ∧ (c₂, s) ⇒ t) :=
begin
  cases ‹(IF b THEN c₁ ELSE c₂, s) ⇒ t›,
    case IfTrue : { exact or.inl ⟨‹↥(bval b s)›, ‹(c₁, s) ⇒ t›⟩ },
    case IfFalse : { exact or.inr ⟨‹¬↥(bval b s)›, ‹(c₂, s) ⇒ t›⟩ }
end

lemma while {b : bexp} {c : com} {s t : state} (h : (WHILE b DO c, s) ⇒ t) :
  (¬bval b s ∧ t = s) ∨ (bval b s ∧ ∃ (s₁ : state), (c, s) ⇒ s₁ ∧ (WHILE b DO c, s₁) ⇒ t) :=
begin
  cases ‹(WHILE b DO c, s) ⇒ t›,
    case WhileTrue : { 
      have : ∃ (s₁ : state), (c, s) ⇒ s₁ ∧ (WHILE b DO c, s₁) ⇒ t := 
        ⟨h_s₂, ⟨‹(c, s) ⇒ h_s₂›, ‹(WHILE b DO c, h_s₂) ⇒ t›⟩⟩,
      exact or.inr ⟨‹↥(bval b s)›, ‹∃ (s₁ : state), (c, s) ⇒ s₁ ∧ (WHILE b DO c, s₁) ⇒ t›⟩ 
    },
    case WhileFalse : { exact or.inl ⟨‹¬↥(bval b s)›, rfl⟩ }
end

end rule_inversion

lemma seq_assoc {c₁ c₂ c₃ : com} {s t : state} :
  (c₁ ;; c₂ ;; c₃, s) ⇒ t ↔ (c₁ ;; (c₂ ;; c₃), s) ⇒ t :=
begin
  split,
    {
      assume : (c₁ ;; c₂ ;; c₃, s) ⇒ t,
      have : ∃ s₁, (c₁ ;; c₂, s) ⇒ s₁ ∧ (c₃, s₁) ⇒ t := 
        rule_inversion.seq ‹(c₁ ;; c₂ ;; c₃, s) ⇒ t›,
      cases ‹∃ s₁, (c₁ ;; c₂, s) ⇒ s₁ ∧ (c₃, s₁) ⇒ t› with s₁,
      cases ‹(c₁ ;; c₂, s) ⇒ s₁ ∧ (c₃, s₁) ⇒ t›,
      have : ∃ s₂, (c₁, s) ⇒ s₂ ∧ (c₂, s₂) ⇒ s₁ := 
        rule_inversion.seq ‹(c₁ ;; c₂, s) ⇒ s₁›,
      cases ‹∃ s₂, (c₁, s) ⇒ s₂ ∧ (c₂, s₂) ⇒ s₁› with s₂,
      cases ‹(c₁, s) ⇒ s₂ ∧ (c₂, s₂) ⇒ s₁›,
      show (c₁ ;; (c₂ ;; c₃), s) ⇒ t, from
        Seq ‹(c₁, s) ⇒ s₂› (Seq ‹(c₂, s₂) ⇒ s₁› ‹(c₃, s₁) ⇒ t›)
    },
    {
      assume : (c₁ ;; (c₂ ;; c₃), s) ⇒ t,
      have : ∃ s₁, (c₁, s) ⇒ s₁ ∧ (c₂ ;; c₃, s₁) ⇒ t :=
        rule_inversion.seq ‹(c₁ ;; (c₂ ;; c₃), s) ⇒ t›,
      cases ‹∃ s₁, (c₁, s) ⇒ s₁ ∧ (c₂ ;; c₃, s₁) ⇒ t› with s₁,
      cases ‹(c₁, s) ⇒ s₁ ∧ (c₂ ;; c₃, s₁) ⇒ t›,
      have : ∃ s₂, (c₂, s₁) ⇒ s₂ ∧ (c₃, s₂) ⇒ t :=
        rule_inversion.seq ‹(c₂ ;; c₃, s₁) ⇒ t›,
      cases ‹∃ s₂, (c₂, s₁) ⇒ s₂ ∧ (c₃, s₂) ⇒ t› with s₂,
      cases ‹(c₂, s₁) ⇒ s₂ ∧ (c₃, s₂) ⇒ t›,
      show (c₁ ;; c₂ ;; c₃, s) ⇒ t, from
        Seq (Seq ‹(c₁, s) ⇒ s₁› ‹(c₂, s₁) ⇒ s₂›) ‹(c₃, s₂) ⇒ t›
    }
end

notation c₁ `∼` c₂ := ∀{s t : state}, (c₁, s) ⇒ t = (c₂, s) ⇒ t

lemma eq_while_ifwhile {b : bexp} {c : com} : WHILE b DO c ∼ IF b THEN (c ;; WHILE b DO c) ELSE SKIP :=
begin
  intros,
  apply iff.to_eq,
  split,
    { 
      intros,
      cases ‹(WHILE b DO c, s) ⇒ t›,
        case WhileFalse : {
          show  (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⇒ s, from
            IfFalse ‹¬↥(bval b s)› Skip
        },
        case WhileTrue : {
          rename ᾰ_s₂ → s',
          show (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⇒ t, from
            IfTrue ‹↥(bval b s)› (Seq ‹(c, s) ⇒ s'› ‹(WHILE b DO c, s') ⇒ t›)
        }
    },
    {
      intros,
      cases ‹(IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s) ⇒ t›,
        case IfTrue : {
          cases ‹(c ;; WHILE b DO c, s) ⇒ t›,
          rename ᾰ_ᾰ_1_s₂ → s',
          show (WHILE b DO c, s) ⇒ t, from
            WhileTrue ‹↥(bval b s)› ‹(c, s) ⇒ s'› ‹(WHILE b DO c, s') ⇒ t›
        },
        case IfFalse : {
          cases ‹(SKIP, s) ⇒ t›,
          show (WHILE b DO c, s) ⇒ s, from
            WhileFalse ‹¬↥(bval b s)›
        }
    }
end

theorem deterministic {c : com} {s : state} :
   ∀{t : state}, (c, s) ⇒ t → ∀{r : state}, (c, s) ⇒ r → (t = r) :=
begin
  assume t : state,
  assume : (c, s) ⇒ t,
  induction ‹(c, s) ⇒ t›,
    case Skip : s {
      assume r : state,
      assume : (SKIP, s) ⇒ r,
      cases ‹(SKIP, s) ⇒ r›,
      reflexivity
    },
    case Assign : s x a {
      assume r : state,
      assume : (x ::= a, s) ⇒ r, 
      cases ‹(x ::= a, s) ⇒ r›,
      reflexivity
    },
    case Seq : c₁ c₂ s s₁ t _ _ ih₁ ih₂ {
      assume r : state,
      assume : (c₁ ;; c₂, s) ⇒ r,
      cases ‹(c₁ ;; c₂, s) ⇒ r›, rename this_s₂ → s₂,
      have : (s₂ = s₁) := (ih₁ ‹(c₁, s) ⇒ s₂›).symm,
      rw ‹s₂ = s₁› at *,
      exact ih₂ ‹(c₂, s₁) ⇒ r›
    },
    case IfTrue : b c₁ c₂ s _ _ _ ih {
      assume r : state,
      assume : (IF b THEN c₁ ELSE c₂, s) ⇒ r,
      cases ‹(IF b THEN c₁ ELSE c₂, s) ⇒ r›,
        case IfTrue : { exact ih ‹(c₁, s) ⇒ r› },
        case IfFalse : { contradiction }
    },
    case IfFalse : b c₁ c₂ s _ _ _ ih {
      assume r : state,
      assume : (IF b THEN c₁ ELSE c₂, s) ⇒ r,
      cases ‹(IF b THEN c₁ ELSE c₂, s) ⇒ r›,
        case IfTrue : { contradiction },
        case IfFalse : { exact ih ‹(c₂, s) ⇒ r› }
    },
    case WhileTrue : b c s s₁ _ _ _ _ ih₁ ih₂ {
      assume r : state,
      assume : (WHILE b DO c, s) ⇒ r,
      cases ‹(WHILE b DO c, s) ⇒ r›,
        case WhileTrue : { 
          rename this_s₂ → s₂,
          have : (s₂ = s₁) := (ih₁ ‹(c, s) ⇒ s₂›).symm,
          rw ‹s₂ = s₁› at *,
          exact ih₂ ‹(WHILE b DO c, s₁) ⇒ r›
        },
        case WhileFalse : { contradiction }
    },
    case WhileFalse : b c s {
      assume r : state,
      assume : (WHILE b DO c, s) ⇒ r,
      cases ‹(WHILE b DO c, s) ⇒ r›,
        case WhileTrue : { contradiction },
        case WhileFalse : { reflexivity }
    }
end

end big_step

inductive small_step : com × state → com × state → Prop
| Assign  {s : state} {x : vname} {a : aexp} :
  small_step (x ::= a, s) (SKIP, s[x ↦ aval a s])

| Seq1 {c₂ : com} {s : state} :
  small_step (SKIP;;c₂, s) (c₂, s)

| Seq2 {c₁ c₁' c₂ : com} {s s' : state} :
  small_step (c₁, s) (c₁', s') →
  small_step (c₁ ;; c₂, s) (c₁';;c₂, s)

| IfTrue {b : bexp} {s : state} {c₁ c₂ : com}:
  bval b s →
  small_step (IF b THEN c₁ ELSE c₂, s) (c₁, s)

| IfFalse {b : bexp} {s : state} {c₁ c₂ : com}:
  ¬bval b s →
  small_step (IF b THEN c₁ ELSE c₂, s) (c₂, s)

| While {b : bexp} {c : com} {s : state} :
  small_step (WHILE b DO c, s) (IF b THEN (c ;; WHILE b DO c) ELSE SKIP, s)

infix ` ↝ `:70 := small_step

open small_step

namespace small_step

end small_step 

end IMP