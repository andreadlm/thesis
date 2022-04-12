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

notation s ` = ` t ` ⦅<= ` l `⦆` := ∀ (x : vname), (sec x <= l) → s x = t x
notation s ` = ` t ` ⦅< ` l `⦆` := ∀ (x : vname), (sec x < l) → s x = t x

lemma noninterference_aexp {s t : pstate} {l : lv} {a : aexp} :
  s = t ⦅<= l⦆ → (secₐ a <= l) → (aval a s = aval a t) :=
begin
  intros,
  induction' a,
    case N : {
      trivial
    },
    case V : x {
      dsimp[secₐ, aval] at *,

      show s x = t x, from ‹s = t ⦅<= l⦆› x ‹sec x ≤ l›
    },
    case Plus : a₁ a₂ ih₁ ih₂ {
      dsimp[secₐ, aval] at *,

      have : (secₐ a₁ <= l) ∧ (secₐ a₂ <= l), by 
        simpa using ‹max (secₐ a₁) (secₐ a₂) ≤ l›,
      cases' ‹(secₐ a₁ <= l) ∧ (secₐ a₂ <= l)›,

      have : aval a₁ s = aval a₁ t, from ih₁ ‹s = t ⦅<= l⦆› ‹(secₐ a₁ <= l)›,
      have : aval a₂ s = aval a₂ t, from ih₂ ‹s = t ⦅<= l⦆› ‹(secₐ a₂ <= l)›,

      show (aval a₁ s + aval a₂ s) = (aval a₁ t + aval a₂ t), by
        rw[‹aval a₁ s = aval a₁ t›, ‹aval a₂ s = aval a₂ t›]
    }
end