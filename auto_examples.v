Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import semantic.
Require Import syntax.
Require Import complete.
Example autosyntax1 : forall Γ p q , Γ ├ ((p → q) → p) → p.
Proof. auto_Plogic. Qed.
Example autosyntax1' : forall Γ p q , Γ ╞ ((p → q) → p) → p.
Proof. auto_Plogic. Qed.
Example autosyntax2 : forall Γ p, Γ ├ (¬p → p) → p.
Proof. auto_Plogic. Qed.
Example autosyntax2' : forall Γ p, Γ ╞ (¬p → p) → p.
Proof. auto_Plogic. Qed.
Example autosyntax3 : forall p, [¬¬p] ├ p.
Proof. auto_Plogic. Qed.
Example autosyntax3' : forall p, [¬¬p] ╞ p.
Proof. auto_Plogic. Qed.
Example autosyntax4 : forall p q r, [p → q]∪[¬(q → r) → ¬p] ├ p → r.
Proof. auto_Plogic. Qed.
Example autosyntax4' : forall p q r, [p → q]∪[¬(q → r) → ¬p] ╞ p → r.
Proof. auto_Plogic. Qed.
Example autosyntax5 : forall p q r, [p → (q → r)] ├ q → (p → r).
Proof. auto_Plogic. Qed.
Example autosyntax5' : forall p q r, [p → (q → r)] ╞ q → (p → r).
Proof. auto_Plogic. Qed.
Example autosyntax6 : forall Γ p q r, Γ∪[p → q]∪[q → r] ├ p → r.
Proof. auto_Plogic. Qed.
Example autosyntax6' : forall Γ p q r, Γ∪[p → q]∪[q → r] ╞ p → r.
Proof. auto_Plogic. Qed.
Example autosyntax7 : forall Γ p q , Γ ├ (q → p) → (¬p → ¬q).
Proof. auto_Plogic. Qed.
Example autosyntax7' : forall Γ p q, Γ ╞ (q → p) → (¬p → ¬q).
Proof. auto_Plogic. Qed.
Example autosyntax8 : forall p q, Φ ├ p → (¬q → ¬(p → q)).
Proof. auto_Plogic. Qed.
Example autosyntax8' : forall p q, ╞ p → (¬q → ¬(p → q)).
Proof. auto_Plogic. Qed.