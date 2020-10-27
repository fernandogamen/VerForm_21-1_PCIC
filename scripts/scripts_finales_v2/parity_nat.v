Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.
Require Import Psatz. (* This provides 'lia' for solving linear integer arithmetic *)


(* 
- - - - - - - - - - - - - - - - - - - -
Some arithmetic lemmas and theorems 
- - - - - - - - - - - - - - - - - - - -
*)
Lemma not_Zero_val : forall (n:nat), S n <> 1 -> n <> 0.
Proof.
intuition.
Qed.


Lemma suc_minus : forall (n:nat), 1<=n -> S(n - 1) = n.
Proof.
intuition.
Qed.

Lemma leq_1_even : forall (n:nat), 1 <= n -> modulo n 2 = 0 -> 1< n.
Proof.
intros.
inversion H.
rewrite <- H1 in H0.
simpl in H0.
intuition.
intuition.
Qed.


Lemma minus_cancellation: forall (n m j:nat), j<=n -> j<=m -> n - j = m - j -> n = m.
Proof.
intuition.
Qed.


Lemma nonZero_le1:forall (n:nat), n <> 0 -> 1 <= n.
Proof.
intuition.
Qed.


Lemma lt_solve:forall (n m:nat), 1 <= n -> n < 2 * m + 1 -> (n - 1) / 2 < m.
Proof.
intros.
apply Nat.div_lt_upper_bound.
intuition.
intuition.
Qed.


(* 
- - - - - - - - - - - - - - - - - - - -
Parity, div, modulo and divmod lemmas and theorems 
- - - - - - - - - - - - - - - - - - - -
*)
Lemma mod_0_1 : forall (i:nat), modulo i 2 = 0 \/ modulo i 2 = 1.
Proof.
intro.
destruct i.
left.
trivial.
simpl.
destruct (snd (divmod i 1 0 0)).
right.
trivial.
left.
trivial.
Qed.


Lemma div_minus: forall (p q t s:nat), 0 < q -> fst (divmod p t (q-1) s) =  fst (divmod p t q s) - 1.
Proof.
intro.
induction p.
intros.
reflexivity.
intros.
simpl.
destruct s.
assert (S q - 1 = S (q - 1)).
rewrite <- minus_Sn_m. 
trivial.
intuition.
rewrite <- H0.
intuition.
rewrite IHp.
trivial.
trivial.
Qed.


Lemma odd_eq: forall(i:nat), (i - 1) / 2 =  S i / 2 - 1.
Proof.
intros.
induction i.
reflexivity. 
simpl.
simpl in IHi.
assert (fst (divmod (i-0) 1 0 1) = fst (divmod i 1 (1-1) 1)).
rewrite <-(minus_n_O i).
reflexivity.
rewrite div_minus in H.
intuition.
constructor.
Qed.


Lemma snd_div: forall (n p q:nat), (snd(divmod n 1 p 0) = snd(divmod n 1 q 0)) /\ (snd(divmod n 1 p 1) = snd(divmod n 1 q 1)).
Proof.
intro.
induction n.
intros.
simpl.
omega.
intros.
simpl.
destruct IHn with (p:=S(p)) (q:=S(q)).
destruct IHn with (p:=p) (q:=q).
intuition.
Qed.


Lemma suc_suc: forall (n:nat), (modulo n 2 = 0 -> modulo (S(S n)) 2 = 0) /\ (modulo n 2 = 1 -> modulo (S(S n)) 2 = 1).
Proof.
intros.
destruct n.
intuition.
destruct (snd_div n 0 1).
intuition.
simpl in H1; simpl.
rewrite <-H.
intuition.
simpl in H1; simpl.
rewrite <-H.
intuition.
Qed.


Lemma even_odd_even:forall (n:nat), (modulo n 2 = 0 -> modulo (S n) 2 = 1) /\ (modulo n 2 = 1 -> modulo (S n) 2 = 0).
Proof.
intro.
induction n.
intuition.
destruct IHn.
destruct (mod_0_1 n).
intuition.
apply suc_suc in H1.
trivial.
intuition.
apply suc_suc in H1.
trivial.
Qed.


Lemma even_odd_even_2:forall (n:nat), (modulo (S n) 2 = 0 -> modulo n 2 = 1) /\ (modulo (S n) 2 = 1 -> modulo n 2 = 0).
Proof.
intros.
destruct (mod_0_1 n).
intuition.
apply even_odd_even in H.
intuition.
intuition.
apply even_odd_even in H.
intuition.
Qed.


Lemma div_leq_1: forall (i r q:nat), 1<=q -> 1 <= fst (divmod i 1 q r).
Proof.
intro.
induction i.
intuition.
intros.
destruct r.
simpl.
intuition.
simpl.
intuition.
Qed.


Lemma even_odd_div: forall (i:nat), (modulo i 2 = 0 -> fst (divmod i 1 0 1) = fst (divmod i 1 0 0)) /\ (modulo i 2 = 1 -> fst (divmod i 1 0 1) = fst (divmod i 1 0 0)-1).
Proof.
intro.
induction i.
intuition.
destruct IHi.
intuition.
destruct (mod_0_1 i).
apply even_odd_even in H2.
intuition.
apply H0 in H2.
simpl.
rewrite div_minus with (q:=1) in H2.
apply minus_cancellation in H2.
intuition.
apply div_leq_1.
trivial.
destruct i.
inversion H1.
simpl.
apply div_leq_1.
trivial.
constructor.
destruct (mod_0_1 i).
apply H in H2.
simpl.
rewrite div_minus with (q:=1) in H2.
intuition.
constructor.
apply even_odd_even in H2.
intuition.
Qed.


Lemma div_2_lq_1 : forall (i:nat), 1 < i -> 1 <= i / 2.
Proof.
intro.
induction i.
intuition.
intros.
simpl.
inversion H.
intuition.
apply IHi in H1.
simpl in H1.
destruct (mod_0_1 i).
apply even_odd_div in H2.
intuition.
apply even_odd_div in H2.
intuition.
Qed.


Lemma mod_i: forall (i:nat), (modulo i 2 = 0 -> (i - 1) / 2 = i / 2 - 1) /\ (modulo i 2 = 1 -> (i - 1) / 2 = i / 2).
Proof.
intros.
induction i.
intuition.
destruct IHi.
intuition.
(* Goal: S i mod 2 = 0 -> (S i - 1) / 2 = S i / 2 - 1 *)
destruct (mod_0_1 i).
apply even_odd_even in H2.
intuition.
apply H0 in H2.
rewrite odd_eq in H2.
simpl (i/2) in H2; simpl ((S i - 1)/2).
rewrite <- minus_n_O.
intuition.
(* Goal: S i mod 2 = 1 -> (S i - 1) / 2 = S i / 2 *)
destruct (mod_0_1 i).
simpl.
rewrite <- minus_n_O.
apply even_odd_div.
trivial.
apply even_odd_even in H2.
intuition.
Qed.


Lemma even_odd_mod: forall (n:nat), ( modulo (S(2 * n)) 2 = 1) /\ (modulo (2 * n) 2 = 0).
Proof.
intros.
induction n.
intuition.
simpl.
simpl in IHn.
rewrite plus_0_r.
rewrite plus_0_r in IHn.
rewrite <-plus_n_Sm.
simpl.
destruct IHn.
destruct (snd_div (n + n) 0 1).
rewrite H1 in H.
rewrite H2 in H0.
intuition.
Qed.
