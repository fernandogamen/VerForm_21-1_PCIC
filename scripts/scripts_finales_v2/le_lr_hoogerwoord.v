Load braunT_nat.

(* Definition of the low extension as proposed by Hogerwword *)
Fixpoint le_hgrwd (b:A) (tree:BTree) : BTree :=
  match tree with 
      E => N b E E
     |N a s t => N b (le_hgrwd a t) s
  end.

Fixpoint lr_hgrwd (tree:BTree) : BTree :=
  match tree with
      E => undefBTree
     |N a E E => E
     |N a s t => N (lookup s 0) t (lr_hgrwd s) (* We know that s <> E since the case where s=E and t=E corresponds to the previous pattern, and the trees we work with are those that satisfy the 'bal' property, see below theorem left_subtree_nonE: bal(N a t1 t2) -> t2 <> E -> t1 <> E. *)
  end.


Lemma equiv_le : forall (t:BTree) (b:A), bal t -> bbal t -> le b t = le_hgrwd b t.
Proof.
intuition.
Qed.


Lemma equiv_lr : forall (t:BTree), bal t -> bbal t -> lr t = lr_hgrwd t.
Proof.
intro.
induction t.
(* t=E *)
reflexivity.
(* t = N a t1 t2 *)
intros.
destruct t1.
(* t1 = E *)
rewrite (leftE_leaf_nat a E t2).
reflexivity.
trivial.
trivial.
(* t1 = N a0 t1_1 t1_2 *)
replace (lr (N a (N a0 t1_1 t1_2) t2)) with (N a0 t2 (lr (N a0 t1_1 t1_2))).
replace (lr_hgrwd (N a (N a0 t1_1 t1_2) t2)) with (N a0 t2 (lr_hgrwd (N a0 t1_1 t1_2))).
rewrite IHt1.
reflexivity.
(* Since we used IHt1, we need to prove its hypothesis *)
inversion H.
trivial.
(* Since we used IHt1, we need to prove its hypothesis *)
inversion H0.
trivial.
(* We prove the replacement  N a0 t2 (lr_hgrwd (N a0 t1_1 t1_2)) = lr_hgrwd (N a (N a0 t1_1 t1_2) t2) *)
reflexivity.
(* We prove the replacement N a0 t2 (lr (N a0 t1_1 t1_2)) = lr (N a (N a0 t1_1 t1_2) t2) *)
simpl.
destruct (bnNonZ (sucBN (bsize t1_1 ⊞ bsize t1_2))).
(* sucBN (bsize t1_1 ⊞ bsize t1_2) <> Z *)
destruct (bsize t1_1 ⊞ bsize t1_2).
discriminate.
simpl.
discriminate.
simpl.
discriminate.
destruct H1.
rewrite H1.
reflexivity.
rewrite H1.
reflexivity.
Qed.
