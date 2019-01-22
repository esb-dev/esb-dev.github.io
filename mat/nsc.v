(*
  Natürliches Schließen in Coq - Tutorium
  © 2019 by Burkhardt Renz, THM
  CC BY-NC-SA 
*)

(** * Natürliches Schließen in Coq *)
Section Natural_Deduction.


(** ** Implikation *)

Section impl_i.

Variables P Q: Prop.

(* Regel rückwärts *)
Example impl_i: P -> Q.
Proof.
  intro H.
  (* Nun muss man einen Beweis finden, der
     Q aus P herleitet *)
Abort.

Example impl_i_f: P -> Q.
Proof.
  assert (P -> Q).
  (* erzeugt neues Subziel P -> Q, das man dann rückwärts
     verwenden muss *)
  intro H.
Abort.

Example impl_i: P -> P.
Proof.
  intro H.
  assumption.
  (* oder exact H. *)
Qed.

Example impl_i_f: P -> P.
  assert (P -> P).
  intro H; assumption.
  assumption.
Qed.

End impl_i.

Check impl_i.

Section impl_e.

Variables P Q: Prop.
Hypothesis (H1: P) (H2: P -> Q).

Example impl_e: Q.
Proof.
  apply H2.
  exact H1.
Qed.

Example impl_e_f: Q.
  apply impl_e.
Qed.

End impl_e.

Check impl_e.

(* Interessantes Beispiel 
   Coq'Art Übung 3.2 *)

Section weak_peirce.

Variable P Q: Prop.

Theorem weak_peirce: ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof. 
  intro H0; apply H0.
  intro H1; apply H1.
  intro H2.
  apply H0.
  intro.
  exact H2.
Qed.

End weak_peirce.

Check weak_peirce.

(** ** Konjunktion *)

Section and_i.

Variables P Q: Prop.
Hypothesis (H1: P) (H2: Q).

Example and_i: P /\ Q.
Proof.
  split.
  - exact H1.
  - exact H2.
Qed.

Variables R: Prop.
Hypotheses (H: P /\ Q -> R).

Example and_i_f: R.
Proof.
  assert (P /\ Q).
  split; assumption.
  (* Jetzt muss man noch R zeigen: *)
  apply H; assumption.
Qed.

End and_i.

Section and_e.

Variables P Q: Prop.
Hypothesis (H: P /\ Q).

Example and_e1: P.
Proof.
  elim H.
  intros.
  assumption.
Qed.

Example and_e1_f: P.
Proof.
  destruct H.
  assumption.
Qed.

Example and_e2: Q.
Proof.
  apply H.
Qed.

End and_e.

Section and_comm.

Variables P Q: Prop.

Theorem and_comm: P /\ Q -> Q /\ P.
Proof.
  intro H.
  elim H.
  intros H1 H2.
  split; assumption.
Qed.

Theorem and_comm': P /\ Q -> Q /\ P.
Proof.
  intro H.
  destruct H as [H1 H2].
  split; assumption.
Qed.

End and_comm.

(* Zerlegende Bindung (_Destructuring_) kann man
   schön einsetzen. *)

Section and_assoc.

Variables P Q R: Prop.

Theorem and_assoc: (P /\ Q) /\ R -> P /\ (Q /\ R).
Proof.
  intro H.
  destruct H as [[H1 H2] H3].
  repeat split; assumption.
Qed.

End and_assoc.

(** ** Disjunktion *)

Section or_i.

Variables P Q: Prop.
Hypothesis (H1: P).

Example or_i1: P \/ Q.
Proof.
  left.
  exact H1.
Qed.

Example or_i1_f: P \/ Q.
Proof.
  assert (P \/ Q).
  left; assumption.
  left; assumption.
Qed.

Hypothesis (H2: Q).

Example or_i2: P \/ Q.
Proof.
  right.
  exact H2.
Qed.

End or_i.

Section or_e.

Variables P Q R: Prop.

Hypothesis (H: P \/ Q) (H1: P -> R) (H2: Q -> R).

Example or_e: R.
Proof.
  elim H.
  - intro Hp. apply H1. assumption.
  - intro Hq. apply H2. assumption.
Qed.

Example or_e': R.
Proof.
  destruct H as [Hp|Hq].
  apply H1; assumption.
  apply H2; assumption.
Qed.

End or_e.

Section or_comm.

Variables P Q: Prop.

Theorem or_comm: P \/ Q -> Q \/ P.
Proof.
  intro H.
  destruct H as [Hp|Hq].
  right; assumption.
  left; assumption.
Qed.

End or_comm.

Section or_assoc.

Variables P Q R: Prop.

Theorem or_assoc: (P \/ Q) \/ R -> P \/ (Q \/ R).
Proof.
  intro H.
  elim H.
  - intro H1; elim H1. 
    -- intro H11; left; assumption.
    -- intro H12; right; left; assumption.
  - intro H2; right; right; assumption.
Qed.

Theorem or_assoc': (P \/ Q) \/ R -> P \/ (Q \/ R).
Proof.
  intro H.
  destruct H as [[H0 | H1] | H2].
  - left; assumption.
  - right; left; assumption.
  - right; right; assumption.
Qed.

End or_assoc.

(** * Negation *)

Section not_i.

Variable P: Prop.
Hypothesis (HP: P -> False).

Example not_i: ~P.
Proof.
  intro H.
  (* Jetzt muss man aus [P] den Widerspruch folgern,
     was wir voraussetzen *)
  apply HP; assumption.
Qed.

End not_i.

Section not_e.

Variables P Q: Prop.

Hypothesis (H: P /\ ~P).

Example not_e: Q.
Proof.
  elim H.
  intros H1 H2.
  elim H2.
  assumption.
Qed.

(* geht auch einfacher *)
Example not_e': Q.
Proof.
  destruct H as [H1 H2].
  elim H2.
  assumption.
Qed.

Example not_e'': Q.
Proof.
  absurd P; destruct H ;assumption.
Qed.

End not_e.

Section double_neg.

Variable P: Prop.

Theorem double_neg: P -> ~~P.
Proof.
  intros H H1.
  elim H1.
  assumption.
Qed.

End double_neg.

Section contraposition.

Variables P Q: Prop.

Theorem contraposition: (P -> Q) -> ~Q -> ~P.
Proof.
  intros H H1 H2.
  elim H1.
  apply H; assumption.
Qed.

End contraposition.

(** ** Allquantor *)

Section quantors.

Variable U: Set.    (* Das Universum *)
Variable S: U -> Prop.

Section forall_i.

Example forall_i: forall x: U, S x -> S x.
Proof.
  intros x H.
  assumption.
Qed.

End forall_i.

Section forall_e.

Variable a: U.

Example forall_e: (forall x: U, S x) -> S a.
Proof.
  intro H.
  apply H.
Qed.

End forall_e.

Section Ex_forall.

Variable T: U -> U -> Prop.
Variable f: U -> U.

Hypothesis T_reflexiv: forall x: U, T x x.
Hypothesis T_f: forall x y: U, T x y -> T x (f y). 

Example Ex: forall x: U, T x (f (f (f x))).
Proof.
  intro x.
  repeat apply T_f.
  apply T_reflexiv.
Qed.

End Ex_forall.

(** ** Existenzquantor *)

Section exists_i.

Variable a: U.

Example exists_i: (forall x: U, S x) -> (exists x: U, S x).
Proof.
  intro H.
  exists a.
  apply H.
Qed.

End exists_i.

Section exists_e.

Example exists_e: (exists x: U, S x) -> ~(forall x: U, ~S x).
Proof.
  intro H.
  intro H1.
  elim H.
  assumption.
Qed.


Example exists_e': (exists x: U, S x) -> ~(forall x: U, ~S x).
Proof.
  intro H.
  destruct H as (x, HS).
  intro HN.
  elim HN with (x:=x).
  assumption.
Qed.


Theorem forall_not_exists_not: (forall x: U, S x) -> ~(exists y: U, ~S y).
Proof.
  intro H.
  intro H1.
  destruct H1 as (x, HS).
  elim HS.
  apply H.
Qed.
End exists_e.


(** ** Gleichheit *)

Section equal_i.

Variable t: U.

Example equal_i: t = t.
Proof.
  reflexivity.
Qed.

End equal_i.

Section equal_e.

Variables t1 t2: U.

Hypothesis (H1: t1 = t2) (H2: S t1).

Example equal_e: S t2.
Proof.
  rewrite <- H1.
  assumption.
Qed.

End equal_e.

Theorem equal_sym: forall x y: U, x = y -> y = x.
Proof.
  intros x y H.
  rewrite <- H.
  reflexivity.
Qed.

End quantors.
End Natural_Deduction.

(* Tatsächlich haben wir Aussagen über Meta-Variablen
   bewiesen: *)

Check or_comm.
(* ==>
or_comm
     : forall P Q : Prop, P \/ Q -> Q \/ P 
*)

Section Use_or_comm.
 
Variables X Y: Prop.
Example or_c: X \/ Y -> Y \/ X.
Proof.
  apply or_comm.
Qed.

End Use_or_comm.

Check forall_not_exists_not.
(* ==>
forall_not_exists_not
     : forall (U : Set) (S : U -> Prop),
       (forall x : U, S x) -> ~ (exists y : U, ~ S y)
*)

(* Allgemeinere Formulierung *)

Lemma all_not_ex_not:
  forall (U: Type) (P: U -> Prop),
    (forall x: U, P x) -> ~ (exists x: U, ~ P x).
Proof.
  intros.
  intro H1.
  elim H1.
  intros x H2.
  elim H2.
  apply H.
Qed.

Check all_not_ex_not.
(* ==>
all_not_ex_not
     : forall (U : Type) (P : U -> Prop),
       (forall x : U, P x) -> ~ (exists x : U, ~ P x):
*)

Section Gentzen.

Variables X Y Z: Prop.

Example Beispiel1: X /\ (Y \/ Z ) -> (X \/ Y) /\ (X \/ Z).
Proof.
  intro H.
  destruct H as [HX [HY | HZ]].
  - split; repeat left; assumption.
  - split; repeat left; assumption.
Qed.


(* bekommt man in Coq auch "geschenkt": *)
Example Beispiel1': X /\ (Y \/ Z ) -> (X \/ Y) /\ (X \/ Z).
Proof.
  tauto.
Qed.


Variables (U: Set) (F: U -> U -> Prop) (G: U -> Prop).

Example Beispiel2: (exists x: U, forall y: U, F x y) ->
                   (forall y: U, exists x: U, F x y).
Proof.
  intros H1 a.
  elim H1.
  intros b H2.
  exists b.
  apply H2.
Qed.

Example Beispiel2': (exists x: U, forall y: U, F x y) ->
                   (forall y: U, exists x: U, F x y).
Proof.
  firstorder.
Qed.

Example Beispiel3: (~ exists x: U, G x) -> (forall y: U, ~ G y).
Proof.
  intros H a ga.
  apply H.
  exists a.
  assumption.
Qed.

End Gentzen.

(** * Charakterisierungen klassischer Logik *)

Section Classical.

Definition peirce         := forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition notnot_e       := forall P : Prop, ~~P -> P.
Definition tnd            := forall P : Prop, P \/ ~P.
Definition dm_not_and_not := forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or  := forall P Q : Prop, (P -> Q) -> (~P \/ Q).

(* Die Aufgabe besteht darin zu zeigen, dass alle diese Aussagen
   äquivalent sind. 
   Siehe Bertot, Aufgabe 5.7 *)

Lemma peirce_notnot_e: peirce -> notnot_e.
Proof.
  unfold peirce.
  intros Hpeirce P H.
  apply (Hpeirce P False).
  intro H1.
  elim H.
  assumption.
Qed.

Lemma notnot_e_tnd: notnot_e -> tnd.
Proof.
  unfold tnd.
  intros Hnotnot_e P.
  apply Hnotnot_e.
  intro H.
  absurd P. (* Um False zu zeigen, zeigt man ~ P und P *)
  - intro H1.
    apply H; left; assumption.
  - apply Hnotnot_e.
    intro H2.
    apply H; right; assumption.
Qed.

Lemma tnd_dm_not_and_not : tnd -> dm_not_and_not.
Proof. 
  intro Htnd.
  unfold dm_not_and_not.
  intros P Q H.
  assert (P \/ ~P).
  apply Htnd.
  assert (Q \/ ~Q).
  apply Htnd.
  elim H0.
  - intro HP; left; exact HP.
  - elim H1.
    -- intro HQ; right; exact HQ.
    -- intros HnQ HnP.
       elim H.
       split; repeat assumption.
Qed.

Lemma dm_implies_to_or : dm_not_and_not -> implies_to_or.
Proof.
  intro Hdm.
  unfold implies_to_or.
  intros P Q H.
  apply Hdm.
  intro H1.
  elim H1.
  intros H2 H3.
  assert P.
  assert (hc: P \/ ~P).
  - apply Hdm.
    intro Hx.
    elim Hx.
    intros Hy Hz.
    apply Hz.
    exact Hy.
  - elim hc.
    -- trivial.
    -- intro H4.
       elim H2.
       exact H4.
  - apply H3.
    apply H.
    exact H0.
Qed.

Lemma implies_to_or_peirce : implies_to_or -> peirce.
Proof.
  intro Himp.
  unfold peirce.
  intros P Q H.
  assert (H1: ~P \/ P).
  - apply Himp.
    trivial.
  - elim H1.
    -- intro H2; apply H.
       intro HP; elim H2.
       exact HP.
    -- trivial.
Qed.

End Classical.
