Require Import Coq.Sets.Ensembles.
Require Import base_pc.
Require Import syntax.

Definition Ax1 (P : Formula -> Prop) :=
  forall p q, P (p → (q → p)).
Definition Ax2 (P : Formula -> Prop) :=
  forall p q r, P ((p → (q → r)) → ((p → q) → (p → r))).
Definition Ax3 (P : Formula -> Prop) :=
  forall p q, P ((¬p → ¬q)→ (q → p)).
Definition MP_rule (P : Formula -> Prop) :=
  forall p q, P (p → q) -> P p -> P q.
Definition Ax_indirect (P : Formula -> Prop):=
  forall p q, P (¬p → ¬q) → ((¬p → q) → p).
Definition Ax_absurdity (P : Formula -> Prop):=
  forall p q, P (p → q) → (p → ¬q) → ¬p.

Global Hint Unfold Ax1 Ax2 Ax3 MP_rule : LP.

Inductive prove_L : Formula -> Prop :=
  | L1_P : Ax1 _
  | L2_P : Ax2 _
  | L3_P : Ax3 _
  | MP_P : MP_rule prove_L.

Notation " ├ p " := (prove_L p)(at level 85).

Global Hint Resolve L1_P L2_P L3_P MP_P : LP L'D PD AD FD.

Theorem eq_prove_deduce : forall p, Φ ├ p <-> ├ p.
Proof.
  split; intros.
  - induction H; eauto with LP. autoL.
  - induction H; autoL.
Qed.

Theorem prove_to_deduce : forall p, ├ p -> forall Γ, Γ ├ p.
Proof.
  intros. induction H; autoL.
Qed.

(*古典命题演算系统：L L' F F'系统*)
(* L'系统 *)
Section classical_logic.
Variable Γ : Ensemble Formula.
Inductive deduce_L' : Formula -> Prop :=
  | L'0 : forall p, p ∈ Γ -> deduce_L' p 
  | L'1 : Ax1 _
  | L'2 : Ax2 _
  | L'3 : forall p q, deduce_L' (¬q → (q → p))
  | L'4 : forall p, deduce_L' ((¬p → p)→ p)
  | L'MP : MP_rule deduce_L'.

Inductive deduce_P : Formula -> Prop :=
  | P0 : forall p, p ∈ Γ -> deduce_P p 
  | P1 : Ax1 _
  | P2 : Ax2 _
  | PMP : MP_rule deduce_P
  | Pindirect : Ax_indirect _.

Inductive deduce_A : Formula -> Prop :=
  | A0 : forall p, p ∈ Γ -> deduce_A p 
  | A1 : Ax1 _
  | A2 : Ax2 _
  | A3 : forall p, deduce_A (¬¬p → p)
  | AMP : MP_rule deduce_A
  | Aabsurdity : Ax_absurdity _.

Inductive deduce_F : Formula -> Prop :=
  | F0 : forall p, p ∈ Γ -> deduce_F p 
  | F1 : Ax1 _
  | F2 : Ax2 _
  | FMP : MP_rule deduce_F
  | Findirect : Ax_indirect _.

End classical_logic.

Notation " Γ ├L' p " := (deduce_L' Γ p)(at level 80).
Notation " Γ ├P p " := (deduce_P Γ p)(at level 80).
Notation " Γ ├A p " := (deduce_A Γ p)(at level 80).
Notation " Γ ├F p " := (deduce_F Γ p)(at level 80).

Global Hint Resolve L'0 L'3 L'4 : L'D.
Global Hint Extern 1 (_ ├L' _) => apply L'1 : L'D.
Global Hint Extern 1 (_ ├L' _) => apply L'2 : L'D.
Global Hint Extern 3 (_ ├L' _) => eapply L'MP : L'D.

Global Hint Extern 2 (_ ├P _) => apply P0 : PD.
Global Hint Extern 1 (_ ├P _) => apply P1 : PD.
Global Hint Extern 1 (_ ├P _) => apply P2 : PD.
Global Hint Extern 3 (_ ├P _) => eapply PMP : PD.
Global Hint Extern 1 (_ ├P _) => apply Pindirect : PD.

Global Hint Extern 2 (_ ├A _) => apply A0 : AD.
Global Hint Extern 1 (_ ├A _) => apply A1 : AD.
Global Hint Extern 1 (_ ├A _) => apply A2 : AD.
Global Hint Extern 1 (_ ├A _) => apply A3 : AD.
Global Hint Extern 3 (_ ├A _) => eapply AMP : AD.
Global Hint Extern 1 (_ ├A _) => apply Aabsurdity : AD.

Global Hint Extern 2 (_ ├F _) => apply F0 : FD.
Global Hint Extern 1 (_ ├F _) => apply F1 : FD.
Global Hint Extern 1 (_ ├F _) => apply F2 : FD.
Global Hint Extern 3 (_ ├F _) => eapply FMP : FD.
Global Hint Extern 1 (_ ├F _) => apply Findirect : FD.

 (*A*)
Theorem UnionA : forall Γ p q, Γ ├A q -> Γ∪[p] ├A q.
Proof. intros. induction H; eauto with AD sets. Qed.

Theorem Deductive_Theorem_A : forall Γ p q, Γ∪[p] ├A q <-> Γ ├A p → q.
Proof.
  split; intros.
  - induction H; eauto with *. ES; eauto with *.
  - apply AMP with p; eauto with *. apply UnionA; auto. Unshelve. auto.
Qed.

Theorem AReduction_absurdity : forall Γ p q, (Γ∪[p]) ├A q ->
   (Γ∪[p]) ├A ¬q -> Γ ├A ¬p.
Proof.
  intros. pose proof (Aabsurdity Γ p q). apply Deductive_Theorem_A in H.
  apply Deductive_Theorem_A in H0. pose proof AMP. unfold MP_rule in H2.
  pose proof (AMP _ _ _ H1 H). eauto with *.
Qed.

Theorem A_rule_Indirect : forall Γ p q, (Γ∪[¬p]) ├A q -> (Γ∪[¬p]) ├A ¬q ->
  Γ ├A p.
Proof.
  intros. assert (Γ ├A ¬¬p). { apply (AReduction_absurdity _ _ _ H H0). }
  eauto with *.
Qed.

Theorem A_Indirect : forall Γ p q, Γ ├A (¬p → ¬q) → ((¬p → q) → p).
Proof.
  intros. repeat (apply -> Deductive_Theorem_A).
  assert (Γ ∪ [¬ p → ¬ q] ∪ [¬ p → q] ├A ¬ p → ¬ q) by eauto with *.
  assert (Γ ∪ [¬ p → ¬ q] ∪ [¬ p → q] ├A ¬ p → q) by eauto with *.
  apply Deductive_Theorem_A in H. apply Deductive_Theorem_A in H0.
  eapply A_rule_Indirect; eauto.
Qed.

Global Hint Resolve A_Indirect : AD.

(*P*)
Theorem UnionP : forall Γ p q, Γ ├P q -> Γ∪[p] ├P q.
Proof. intros. induction H; eauto with *. Qed.

Theorem Deductive_Theorem_P : forall Γ p q, Γ∪[p] ├P q <-> Γ ├P p → q.
Proof.
  split; intros.
  - induction H; eauto with *. ES; eauto with *.
  - apply PMP with p; eauto with *. apply UnionP; auto.
    Unshelve. auto.
Qed.

Theorem P_rule_Indirect : forall Γ p q, Γ∪[¬p] ├P q ->  Γ∪[¬p] ├P ¬q -> Γ ├P p.
Proof.
  intros. pose proof @Pindirect Γ p q. apply Deductive_Theorem_P in H, H0.
  pose proof (PMP _ _ _ H1 H0). pose proof (PMP _ _ _ H2 H); auto.
Qed.

Theorem P_law_double_negation : forall p Γ, Γ ├P ¬¬p → p.
Proof.
  intros. apply Deductive_Theorem_P.
  apply P_rule_Indirect with ¬p; eauto with *.
Qed.

Global Hint Resolve P_law_double_negation  : PD.

Theorem P_absurdity : forall Γ p q, Γ ├P (p → q) → (p → ¬q) → ¬p.
Proof.
  intros. repeat (apply -> Deductive_Theorem_P).
  pose proof (Pindirect Γ ¬p q).
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├P(¬ ¬ p → ¬ q) → (¬ ¬ p → q) → ¬ p).
  { eauto with *. }
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├P(p → ¬ q)) by eauto with *.
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├P(¬ ¬ p → ¬ q)).
  { eauto with *. } pose proof (PMP _ _ _ H0 H2).
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├P(p → q)) by eauto with *.
  assert (Γ ∪ [p → q] ∪ [p → ¬ q] ├P(¬ ¬ p → q)) by eauto with *.
  eauto with *.
Qed.
Global Hint Resolve P_absurdity : PD.

(* L' *)
Theorem UnionL' : forall p q Γ, Γ ├L' q -> Γ∪[p] ├L' q.
Proof. intros. induction H; eauto with *. Qed.

Theorem Deductive_L' : forall p q Γ, Γ∪[p] ├L' q <-> Γ ├L'p → q.
Proof.
  split; intros.
  - induction H; eauto with *. ES; eauto with *.
  - apply L'MP with p; eauto with *. apply UnionL'; auto.
    Unshelve. auto.
Qed.

Theorem L'indirect: forall p q Γ, Γ∪[¬p] ├L' q ->  Γ∪[¬p] ├L' ¬q
  -> Γ ├L' p.
Proof.
  intros. assert (Γ∪[¬p] ├L' q→p); eauto with *.
  assert (Γ∪[¬p] ├L' p); eauto with *. apply Deductive_L' in H2.
  eauto with *.
Qed.

Theorem L'_indirect: forall p q Γ, Γ ├L' (¬ p → ¬ q) → (¬ p → q) → p.
Proof.
  intros. apply Deductive_L'. apply -> Deductive_L'.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬ p → ¬ q) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬ p → q) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬ p) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' ¬q) by eauto with *.
  assert (Γ∪[¬ p → ¬ q]∪[¬ p → q]∪[¬ p] ├L' q) by eauto with *.
  eapply L'indirect; eauto.
Qed.

Global Hint Resolve L'_indirect : L'D.

Theorem eq_PA : forall p Γ, Γ ├P p <-> Γ ├A p.
Proof.
  split; intros; induction H; eauto with *.
Qed.

Theorem L'_to_L : forall p Γ, Γ ├L' p -> Γ ├ p.
Proof.
  intros. induction H; eauto with *.
Qed.

Theorem L_to_P : forall p Γ, Γ ├ p -> Γ ├P p.
Proof.
  intros. induction H; eauto with *.
  repeat (apply -> Deductive_Theorem_P).
  apply P_rule_Indirect with q; eauto with *.
  apply PMP with ¬ p; eauto with *.
Qed.

Theorem P_to_L' : forall p Γ, Γ ├P p -> Γ ├L' p.
Proof.
  intros. induction H; eauto with *.
Qed.