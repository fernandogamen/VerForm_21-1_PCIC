Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.
Require Import Psatz. (* This provides 'lia' for solving linear integer arithmetic *)

Load removals.
Load parity_nat.


(* Definition of the size function*)
Fixpoint size (t:BTree) : nat :=
 match t with
  |E => 0
  |N x s t => S(size s + size t)
 end.

(* Every Braun tree most be a balanced tree according to the next definition *)
Inductive bal : BTree -> Prop :=
  |balE  : bal E
  |balN : forall (a:A) (s t: BTree), bal s -> bal t -> size t <= size s -> size s <= S(size t) -> bal (N a s t).


(* Definition of the lookup function *)
Fixpoint lookup (t:BTree) (i: nat) : A :=
 match t,i with
  |E,i => undefA
  |N x s t,0 => x
  |N x s t,i => if beq_nat (modulo i 2) 1 then lookup s (div i 2) else lookup t (div i 2-1)
 end.


(* Definition of the update function *)
Fixpoint upd (t:BTree) (i: nat) (x : A) : BTree :=
 match t,i with
  |E,i => undefBTree
  |N y s t, 0 =>  N x s t
  |N y s t,i => if beq_nat (modulo i 2) 1 then N y (upd s (div i 2) x) t  else N y s (upd t (div i 2-1) x)
 end.


(* Definition of the high extension as proposed by Hoogerwoord *)
Fixpoint he_hgrwd (b:A) (tree:BTree) : BTree :=
  match tree with 
        E => N b E E
      | N a s t => if beq_nat (modulo (size tree - 1) 2) 0 
                   then N a (he_hgrwd b s) t
                   else N a s (he_hgrwd b t)
  end.


(* Definition of the high removal as proposed by Hoogerwoord *)
Fixpoint hr_hgrwd (tree:BTree) : BTree := 
  match tree with
       E => undefBTree (* We add this case because Coq requires us to write total functions *)
     | N a E E => E
     | N a s t => if beq_nat (modulo (size tree - 2) 2) 0 
                   then N a (hr_hgrwd s) t
                   else N a s (hr_hgrwd t) (* We know that s <> E since the case where s=E and t=E corresponds to the previous pattern, and the trees we work with are those that satisfy the 'bal' property, see below theorem left_subtree_nonE: bal(N a t1 t2) -> t2 <> E -> t1 <> E. *)
  end.


(* 
- - - - - - - - - - - - - - - - - - - -
Braun trees related lemmas and theorems 
- - - - - - - - - - - - - - - - - - - -
*)
Lemma size_Z_nat: forall (t : BTree), size t = 0 -> t = E.
Proof.
intros.
destruct t.
trivial.
simpl in H.
symmetry in H.
contradict H.
apply O_S.
Qed.


Lemma size_non0: forall (t1 t2:BTree), t1 <> E -> t2 <> E -> size t1 + size t2 <> 0.
Proof.
intros.
apply nonE_tree in H.
destruct H; destruct H; destruct H.
apply nonE_tree in H0.
destruct H0; destruct H0; destruct H0.
rewrite H; rewrite H0.
simpl.
apply Nat.neq_succ_0.
Qed.



Theorem leftE_leaf_nat : forall (a : A) (t1 t2 : BTree),
       bal (N a t1 t2) -> t1 = E -> t2 = E.
Proof.
intros.
inversion H.
rewrite H0 in H6.
simpl in H6.
inversion H6.
apply size_Z_nat in H9.
trivial.
Qed.


Theorem rightE_nat
     : forall (a : A) (t1 t2 : BTree ),
       bal (N a t1 t2) ->
       t2 = E -> t1 = E \/ (exists aa : A, t1 = N aa E E).
Proof.
intros.
inversion H.
rewrite H0 in H6.
simpl in H6.
inversion H6.
symmetry in H9.
apply size_Z_nat in H9.
intuition.
rewrite H0 in H7.
simpl in H7.
inversion H7.
destruct t1.
intuition.
simpl in H11.
apply eq_add_S in H11.
apply plus_is_O in H11.
destruct H11.
apply size_Z_nat in H10.
apply size_Z_nat in H11.
right.
exists a1.
rewrite H10.
rewrite H11.
trivial.
inversion H11.
apply size_Z_nat in H13.
intuition.
Qed.

Theorem left_subtree_nonE : forall (a:A) (t1 t2:BTree), bal(N a t1 t2) -> t2 <> E -> t1 <> E.
Proof.
intros.
destruct (eq_btree_dec t1 E).
apply (leftE_leaf_nat a t1 t2) in e.
intuition.
trivial.
trivial.
Qed.



Lemma bal_size : forall (a:A) (t1 t2: BTree), bal (N a t1 t2) -> size t1 = S(size t2) \/ size t1 = size t2.
Proof.
intros.
inversion H.
omega.
Qed.



Theorem bal_size_l
     : forall (a : A) (t1 t2 : BTree),
       bal (N a t1 t2) ->
       size (N a t1 t2) <= 2*size t1 + 1.
Proof.
intros.
inversion H.
simpl.
intuition.
Qed.




Theorem bal_size_r
     : forall (a : A) (t1 t2 : BTree),
       bal (N a t1 t2) ->
       size (N a t1 t2) = 2*(size t2)+1 \/
       size (N a t1 t2) = 2*(size t2)+2.
Proof.
intros.
simpl.
destruct (bal_size a t1 t2).
trivial.
intuition.
intuition.
Qed.


Lemma even_index_btree : forall (i:nat) (a:A) (t1 t2:BTree), i<>0 -> bal (N a t1 t2) -> i mod 2 = 0 -> i < size (N a t1 t2) -> i/2 - 1 < size t2.
Proof.
intros.
assert (iEven := H1).
apply mod_i in H1.
destruct (bal_size_r a t1 t2).
trivial.
(* Case 1: size (N a t1 t2) = 2 * size t2 + 1 *)
rewrite H3 in H2.
apply lt_solve in H2.
rewrite H1 in H2.
trivial.
intuition.
(* Case 2: size (N A a t1 t2) = 2 * size t2 + 2 *)
rewrite H3 in H2.
inversion H2.
assert (i = S(2*size t2)).
intuition.
rewrite H4 in iEven.
assert (modulo (S (2 * size t2)) 2 = 1).
apply even_odd_mod.
rewrite H6 in iEven.
intuition.
(* i < 2 * size t2 + 1 *)
assert (i < 2 * size t2 + 1).
intuition.
apply lt_solve in H6.
rewrite H1 in H6.
trivial.
intuition.
Qed.



Lemma odd_index_btree : forall (i:nat) (a:A) (t1 t2:BTree), bal (N a t1 t2) -> i mod 2 = 1 -> i < size (N a t1 t2) -> i/2 < size t1.
Proof.
intros.
destruct i.
simpl in H0.
intuition.
apply mod_i in H0.
apply (bal_size_l a t1 t2) in H.
assert (S i < 2 * size t1 + 1).
intuition.
apply lt_solve in H2.
rewrite H0 in H2.
trivial.
intuition.
Qed.



Lemma size_even : forall (a:A) (t1 t2:BTree), size t1 = S(size t2) -> modulo (size (N a t1 t2)) 2 = 0.
Proof.
intros.
simpl (size (N a t1 t2)).
rewrite H.
replace (S (S(size t2) + size t2)) with (2*(S(size t2))).
apply even_odd_mod.
intuition.
Qed.


Lemma size_odd : forall (a:A) (t1 t2:BTree), size t1 = size t2 -> modulo (size (N a t1 t2)) 2 = 1.
Proof.
intros.
simpl (size (N a t1 t2)).
rewrite H.
replace (S (size t2 + size t2)) with (S(2*(size t2))).
apply even_odd_mod.
intuition.
Qed.



Lemma parity_nat_bn: forall (n:nat), (modulo n 2 = 1 -> toBN n = U (toBN (n/2))) /\ (n <> 0
 -> modulo n 2 = 0 ->  toBN n = D (toBN (n/2 - 1))).
Proof.
intros.
induction n.
(* Base case: n=0 *)
intuition.
inversion H.
(*Inductive step: n= Sn *)
destruct (eq_nat_dec (S n) (S 0)).
(* S n = S 0 *)
apply eq_add_S in e.
rewrite e.
intuition.
(* S n <> 1 *)
destruct IHn.
split.
(* S n mod 2 = 1 -> toBN (S n) = U (toBN (S n / 2)) *)
intros.
simpl.
apply even_odd_even_2 in H1.
assert (nEven := H1).
apply not_Zero_val in n0.
apply H0 in H1.
rewrite H1.
simpl.
rewrite sucBN_toBN.
rewrite suc_minus.
apply even_odd_div in nEven.
rewrite nEven.
trivial.
apply nonZero_le1 in n0.
apply leq_1_even in n0.
apply div_2_lq_1.
trivial.
trivial.
trivial.
(* S n <> 0 -> S n mod 2 = 0 -> toBN (S n) = D (toBN (S n / 2 - 1)) *)
intros.
apply even_odd_even_2 in H2.
assert (nOdd := H2).
apply H in H2.
simpl.
rewrite H2.
simpl.
apply even_odd_div in nOdd.
rewrite nOdd.
trivial.
Qed.


Lemma parity_nat_bn_tree: forall (t:BTree), bal t -> t<>E -> ((modulo (size t) 2 = 1 -> (exists (b:BN), bsize t = U b)) /\ (modulo (size t) 2 = 0 -> (exists (b:BN), bsize t = D b))).
Proof.
intros t Hbal H.
induction t.
(* t=E *)
intuition.
(* t=N a t1 t2 *)
destruct (eq_btree_dec t1 E).
(* t1 = E *)
assert (f:=e).
apply (leftE_leaf_nat a t1 t2) in e.
rewrite e.
rewrite f.
simpl.
intuition.
exists Z.
trivial.
inversion H0.
trivial.
(* t1 <> E*)
destruct (eq_btree_dec t2 E).
(* t2 = E *)
assert (f:=e).
apply (rightE_nat a t1 t2) in e.
destruct e.
intuition.
destruct H0.
rewrite H0.
rewrite f.
simpl.
intuition.
inversion H1.
exists Z.
trivial.
trivial.
(* t2 <> E *)
destruct IHt1.
inversion Hbal.
trivial.
trivial.
destruct IHt2.
inversion Hbal.
trivial.
trivial.
split.
(* size (N a t1 t2) mod 2 = 1 -> exists b : BN, bsize (N a t1 t2) = U b *)
intros.
destruct (bal_size a t1 t2).
trivial.
(* size t1 = size t2 + 1 *)
apply (size_even a t1 t2) in H5.
rewrite H4 in H5.
inversion H5.
(* size t1 = size t2 *)
simpl.
destruct (mod_0_1 (size t2)).
(* size t2 mod 2 = 0 *)
destruct H1.
rewrite <- H5 in H6.
trivial.
destruct H3.
trivial.
exists (sucBN (sucBN (x ⊞ x0))).
rewrite H1.
rewrite H3.
reflexivity.
(* size t2 mod 2 = 1 *)
destruct H0.
rewrite <- H5 in H6.
trivial.
destruct H2.
trivial.
exists (sucBN (x ⊞ x0)).
rewrite H0.
rewrite H2.
reflexivity.
(* size (N a t1 t2) mod 2 = 0 -> exists b : BN, bsize (N a t1 t2) = D b *)
intros.
destruct (bal_size a t1 t2).
trivial.
(* size t1 = S(size t2) *)
simpl.
destruct (mod_0_1 (size t2)).
(* size t2 mod 2 = 0 *)
destruct H0.
rewrite H5.
apply even_odd_even.
trivial.
destruct H3.
trivial.
exists (sucBN (x ⊞ x0)).
rewrite H0.
rewrite H3.
reflexivity.
(* size t2 mod 2 = 1 *)
destruct H1.
rewrite H5.
apply even_odd_even.
trivial.
destruct H2.
trivial.
exists (sucBN (x ⊞ x0)).
rewrite H1.
rewrite H2.
reflexivity.
(* size t1 = size t2 *)
apply (size_odd a t1 t2) in H5.
rewrite H4 in H5.
inversion H5.
Qed.


(* - - - - - - - - - - - - - - - - - - - - - - - - - -
Property 0 of Hoogerwood's paper:
bal <a,s,t> /\ #<a,s,t>=d+1 -> #s = d 'div' 2 + d 'mod' 2 /\ #t = d 'div' 2
- - - - - - - - - - - - - - - - - - - - - - - - - - *)
Lemma prop_0 : forall (a:A) (s t:BTree) (d:nat), bal(N a s t) -> size (N a s t) = S d -> size s = d / 2 + d mod 2 /\ size t = d / 2.
Proof.
intros.
simpl (size (N a s t)) in H0.
apply eq_add_S in H0.
inversion H.
assert (d mod 2 < 2).
apply (Nat.mod_bound_pos d 2).
intuition.
intuition.
rewrite (Nat.div_mod d 2) in H0.
intuition.
intuition.
Qed.
