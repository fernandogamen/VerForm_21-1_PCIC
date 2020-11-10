Section LogMinimal.

Variables p q r s t x l m:Prop.

Theorem DilemaC : (p -> q) -> (r -> s) -> p \/ r -> q \/ s. 
Proof.
intros.
destruct H1.
- left.
  exact (H H1).
(*   apply H.
  assumption.
 *)- right.
 apply (H0 H1).
(*   apply H0.
  assumption. *)
Qed.

Print DilemaC.

Theorem DilemaC2 : (p -> q) -> (r -> s) -> p \/ r -> q \/ s. 
Proof.
intros.
destruct H1.
left.
apply H. 
trivial.
right.
exact (H0 H1).
Qed.


Theorem Absorcion: p <-> p \/ (p /\ q).
Proof.
unfold iff.
split.
intros.
left.
trivial.
intros.
destruct H.
trivial.
destruct H.
trivial.
Qed.



Theorem Distrib : p \/ (q /\ r) -> (p \/ q) /\ (p \/ r).
Proof.
intros.
split.
elim H.
intro.
left.
assumption.
intro.
right.
elim H0.
intros.
assumption.
elim H.
intros.
left.
assumption.
intros.
elim H0.
intros.
right.
assumption.
Qed.

Print Distrib.

Theorem Distrib2 : p /\ (q \/ r) -> (p /\ q) \/ (p /\ r).
Proof.
intros.
destruct H.
destruct H0.
left.
split.
trivial.
trivial.
right.
split.
trivial.
trivial.
Qed.


Theorem DisyImp: p \/ q -> (p -> q) -> q.
Proof.
intros.
destruct H as [H1|H2].
apply H0.
trivial.
trivial.
Qed.




Theorem SyssImp : (p <-> q) -> ((p -> r) <-> (q -> r)).
Proof.
intros.
unfold iff in H.
unfold iff.
split.
intros.
destruct H.
exact (H0 (H2 H1)).
intros.
destruct H.
apply H0.
apply H.
trivial.
Qed.




Theorem SyssImp2 : (p <-> q) -> ((p -> r) <-> (q -> r)).
Proof.
intros.
unfold iff.
split.
intros.
apply H0.
destruct H.
apply H2.
apply H.
apply H2.
trivial.
intros.
apply H0.
destruct H.
apply H.
apply H2.
apply H.
trivial.
Qed.

Hypotheses b z c d:Prop.

Theorem Argumento1: (b /\ z) /\ (z -> c /\ d) /\ (c /\ b -> q) -> q \/t.
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [H2 H3].
left.
apply H3.
split.
destruct H1 as [H4 H5].
apply H2.
trivial.
destruct H1.
trivial.
Qed.


Hypotheses  (H1: (x \/ p) /\ q -> l)
            (H2: m \/ q -> s /\ t)
            (H3: (s /\ t) /\ l -> x)
            (H4: p -> q).


Theorem Argumento2: m /\ p -> x.
Proof.
intros.
apply H3.
destruct H.
split.
apply H2.
left.
trivial.
apply H1.
split.
right.
trivial.
apply H4.
trivial.
Qed.


End LogMinimal.



Section NegMinimal.

Variables p q r s t:Prop.


Theorem negacion: p -> ~~p.
Proof.
intros.
unfold not.
intros.
apply H0.
assumption.
Qed.

Theorem nonoTExc: ~~(p \/ ~p).
Proof.
unfold not.
intros.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.





Theorem NegImp: (p -> q) -> (p -> ~q) -> ~p.
Proof.
intros.
unfold not.
intro.
assert q.
apply H.
assumption.
assert (~q).
apply H0.
assumption.
unfold not in H3.
apply H3.
assumption.
Qed.

Theorem NegImpConj: p /\ ~q -> ~(p -> q).
Proof.
intro.
unfold not.
intro.
destruct H.
assert q.
apply H0.
trivial.
apply H1.  (* Obsérvese que no hay necesidad de desdoblar la definición de ~*)
trivial.
Qed.





Theorem dmorganO : ~ ( p \/ q ) <-> ~p /\ ~q.
Proof.
unfold iff.
split.
unfold not.
intro.
split.
intro.
apply H.
left.
assumption.

intros.
apply H.
right.
assumption.

unfold not.
intros.
elim H.
intros.
elim H0.
exact H1.
exact H2.
Qed.


Theorem defimp: (~p \/ q) -> (p -> q).
Proof.
unfold not.
intros.
elim H.
intros.
elim H1.
assumption.
intro;assumption.
Qed.


Theorem defimp2: (~p \/ q) -> p -> q.
Proof.
intros.
unfold not in H.
destruct H.
elim H.
trivial.
trivial.
Qed.


Theorem Contrapositiva: (p -> q) -> (~q -> ~p).
Proof.
intros.
unfold not in H0.
unfold not.
intro.
apply H0.
apply H.
trivial.
Qed.


Theorem ContrapositivaNegDebil: (p -> ~q) <-> (q -> ~p).
Proof.
unfold iff.
split.
intros.
intro.
apply H.
assumption.
assumption.
intros.
intro.
apply H.
exact H1. 
exact H0.
Qed. 

End NegMinimal.



Section NegIntuicionista.

Variables p q r s t:Prop.

Theorem ExFalso: False -> p.
Proof.
intros.
elim H. 
Qed.


Theorem texcimp: (p \/ ~p) -> ~~p -> p.
Proof.
unfold not.
intros.
elim H.
intuition.
intros.
exfalso.
apply H0.
trivial.
Qed.




Theorem Absurdo: p /\ ~p -> q.
Proof.
intros.
destruct H.
unfold not in H0.
elim H0.
trivial.
Qed.

Check Absurdo.

Check absurd.


Theorem SilogismoDisy: (p \/ q) /\ ~p -> q.
Proof.
intro.
destruct H.
destruct H.
absurd p.
trivial.
trivial.
trivial.
Qed.






Theorem SyssNeg: (p <-> q) <-> (~p <-> ~ q).
Proof.
unfold iff.
split.
intros.
destruct H.
split.
intros.
unfold not.
intros.
apply H1.
apply H0; assumption.
intros.
intro.
apply H1;apply H;assumption.
intros.
destruct H.
split.
intro.
exfalso.
apply H.
apply H0.
apply H.
apply H0.
Admitted.


End NegIntuicionista.


Section LogPred.

Hypotheses (A:Type)

           (P Q: A -> Prop)
           (R : A -> A -> Prop)
           (f : A -> A)
           (a b : A).


Check P a.

Check P a -> Q b.

Check R b.

Check R (f a) (f (f b)).

Check forall x:A, R a x -> R x a.

Check exists x:A, ~ R x x.


Theorem Socrates: (forall x:A, P x -> Q x) /\ P a -> Q a.
Proof.
intros.
destruct H as [P1 P2].
apply P1.
exact P2.
Qed.

Print Socrates.

Theorem DistrAY: (forall x:A, P x /\ Q x) <-> (forall x:A,P x) /\ (forall x:A, Q x).
Proof.
unfold iff.
split.
intros.
split.
intro x0.
destruct H with x0.   (* o bien elim H with x0. *)
exact H0.
intro y0.
elim H with y0.
intros C D.
exact D.
intro E.
destruct E as [C1 C2].
intro z0.
split.
apply C1. 
apply C2.
Qed.

Theorem DistrAO: (forall x:A,P x) \/ (forall x:A, Q x) -> (forall x:A, P x \/ Q x).
Proof.
intro.
destruct H as [H1|H2].
intro x0.
left.
apply H1.
intro y0.
right.
apply H2.
Qed.

Theorem AA: (forall x y:A, R x y) -> forall y x: A, R y x.
Proof.
intro H.
intros y0 x0.
apply H.
Qed.


Theorem AMPN: (forall x:A, P x -> ~ Q x) -> (forall x:A, P x) -> forall z:A, ~ Q z.
Proof.
intros H1 H2.
intro z0.
apply H1.
apply H2.
Qed.




Hypothesis C:Prop.

Theorem PrenexY:  (C /\ forall x:A, P x ) <-> forall x:A, C /\ P x.
Proof.
unfold iff.
split.
- intro H.
  destruct H.
  intro x0.
  split.
  + exact H.
  + apply H0.
- intro K.
split. 
+destruct K with a.
exact H.
+ intro z0.
apply K.
Qed.




Theorem Ex1: P a -> exists x:A, P x.
Proof.
intro.
exists a.
trivial.
Qed.


Theorem EDY: (exists x:A, P x /\ Q x) -> (exists x:A, P x) /\ (exists x:A, Q x).
Proof.
intro H.
split.
destruct H.
destruct H.
exists x.
exact H.
elim H. 
intro z0.
intro K.
destruct K as [K1 K2].
exists z0.
exact K2.
Qed.




Theorem EDO: (exists x:A, P x \/ Q x) <-> (exists x:A, P x) \/ (exists x:A, Q x).
Proof.
unfold iff.
split.
intro H.
destruct H.
destruct H as [H1|H2].
left; exists x;trivial.
right; exists x; trivial.
intro I.
destruct I as [I1|I2].
destruct I1.
exists x.
left;exact H.
destruct I2.
exists x;right;exact H.
Qed.


Theorem AE: (exists x:A, forall y:A , R x y) -> forall y:A, exists x:A, R x y.
Proof.
intro H.
intro y0.
destruct H.
exists x.
apply H.
Qed.


Theorem PrenexImp : ((exists x:A, P x) -> C) <-> forall x:A, P x -> C.
Proof.
Admitted.


Theorem DMorganG: (exists x:A, ~ P x) -> ~ forall x:A, P x.
Proof.
intro.
intro.
destruct H.
apply H.
apply H0.
Qed.

End LogPred.


Require Import Classical.

Parameters (p q r s u v C:Prop)
           (A: Set)
           (a z:A)
           (P Q S: A -> Prop)
           (R: A -> A -> Prop).




Check classic.

Check classic u.

Check classic (u\/v).

Check NNPP.

Check NNPP v.

Check NNPP (u -> v).

Theorem edn: ~~p <-> p.
Proof.
unfold iff.
split.
exact (NNPP p).
intros.
unfold not.
intros.
exact (H0 H).
Qed.

Print edn.
Print NNPP.
Print classic.



Theorem ContraPos: (p -> q) <-> (~q -> ~p).
Proof.
unfold iff.
split.
intuition.
intros.
assert (q \/ ~q).
exact (classic q).
destruct H1.
exact H1.
absurd p.
exact (H H1).
exact H0.
Qed.

Print ContraPos.

Search or.

Theorem DefImp: (p -> q) <-> ~p \/ q.
Proof.
unfold iff.
split.
intro.
assert (p\/~p).
exact (classic p).
destruct H0.
right;exact(H H0).
left;assumption.
intros.
destruct H.
absurd p;trivial;trivial.
trivial.
Qed.

Theorem TEDebil: ((p -> q) -> q) \/ (p->q).
Proof. 
assert ((p->q)\/ ~(p ->q)).
exact (classic(p->q)).
destruct H as [I|N].
right;trivial.
left;intro.
absurd (p -> q);trivial;trivial.
Qed.

Lemma dMorganY: forall p q:Prop, ~(p/\q) <-> ~p \/ ~q.
Proof. Admitted.

Lemma dMorganO: forall p q:Prop, ~(p\/q) <-> ~p /\ ~q.
Proof. Admitted.


Check dMorganY.
Check dMorganO.

Lemma dMorganOi: forall p q:Prop, ~(p\/q) -> ~p /\ ~q.
Proof.
intros p q.
assert (~ (p \/ q) <-> ~ p /\ ~ q).
exact (dMorganO p q).
destruct H.
exact H.
Qed.







Lemma NegImpC: ~(p->q) -> p /\ ~ q.
Proof.
intros.
cut (~~p/\~q).
intros.
destruct H0.
split.
exact ((NNPP p) H0).
trivial.
cut(~(~p \/ q)).
exact (dMorganOi (~p) q ).

contradict H.
intros.
destruct H.
absurd p; assumption; assumption.

assumption.
Qed.


Theorem GoedelDummet: (p -> q) \/ (q -> p).
Proof.
enough ((p -> q) \/ ~(p->q)).
destruct H as [I|N]. 
left;trivial.
enough (p /\ ~ q).
destruct H as [P NQ].
right.
intro.
absurd q;assumption.

(* Versión cut*)
cut (~ (p -> q) -> p /\ ~ q).
intros.
exact (H N).
exact NegImpC.
exact (classic (p-> q)).

(* Versión assert *)
(*
assert (~ (p -> q) -> p /\ ~ q).
exact NegImpC.
exact (H N).
exact (classic (p-> q)).
*)
Qed.

Check GoedelDummet.


Theorem PrenexO:  (C \/ forall x:A, P x ) <-> forall x:A, C \/ P x.
Proof.
unfold iff.
split.
intro D.
destruct D as [D1|D2].
intro x0.
left.
trivial.
intro y0.
right.
apply D2.
intro H.
cut (C \/ ~ C).
intro T.
destruct T as [T1|T2].
left;trivial.
right.
intro z0.
destruct H with z0.
exfalso.
exact (T2 H0).
exact H0.
exact (classic C).
Qed.

Theorem DMorganGb:  (~ forall x:A, P x) -> (exists x:A, ~ P x).
Proof.
intro H.
cut (~~ exists x:A,~P x).
exact (NNPP (exists x:A,~P x)).
intro N.
apply H.
intro z.
cut (~~ P z).
exact (NNPP (P z)).
intro.
apply N.
exists z.
exact H0.
Qed.





Theorem Bebedor: exists x:A, P x -> forall y:A, P y.
Proof.
assert ((forall y:A, P y) \/ ~(forall y:A, P y)).
exact (classic (forall y:A, P y)).
destruct H as [H1|H2].
exists a.
intro.
exact H1.
cut (exists z:A, ~ P z).
intro E.
destruct E as [z].
exists z.
intro.
exfalso.
exact (H H0).
cut (~ forall z:A,P z).
exact (DMorganGb).
exact H2.
Qed.


Theorem Barbero:  ~ exists x, forall y, R x y <-> ~ R y y.
Proof.
intro E.
destruct E.
destruct H with x.
assert (R x x \/ ~ R x x).
exact (classic (R x x)).
destruct H2 as [R1|R2].
apply H0.
trivial.
trivial.
apply H0.
exact (H1 R2).
exact (H1 R2).
Qed.
