Load braunT_bn.


Fixpoint lookup_bn (t:BTree) (b: BN) : A :=
 match t,b with
  |E, b => undefA
  |N x s t,Z => x 
  |N x s t, U a => lookup_bn s a
  |N x s t, D a => lookup_bn t a
 end.



Fixpoint update (t:BTree) (b: BN) (x : A) : BTree :=
 match t,b with
  |E, b => undefBTree
  |N y s t, Z =>  N x s t
  |N y s t, U a => N y (update s a x) t
  |N y s t, D a => N y s (update t a x)
 end.


Check bbal_inv.


(*Generalizable Variables t x b.*)


Lemma bsize_upd: forall (t:BTree) (x:A) (b:BN), b <BN bsize t -> bsize t = bsize (update t b x).
Proof.
intro t.
induction t.
(* Base case *)
intuition.
inversion H.
(* Inductive step *)
intros.
destruct (bbal_inv (N a t1 t2)).
discriminate.
destruct H0.
rewrite H0 in H.
simpl in H.
inversion H.
(* b = Z *)
intuition.
(* U a0 = b, a < Z *)
inversion H3.
(* D a0 = b, a < Z *)
inversion H3.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
destruct H2.
inversion H3.
destruct b.
(* b = Z *)
intuition.
(* b = U b*)
simpl.
rewrite H6 in IHt1.
rewrite (IHt1 x b).
reflexivity.
apply (lt_U_bsize b x0 x1 x2).
rewrite H3 in H.
trivial.
(* b = D b *)
simpl.
rewrite H7 in IHt2.
rewrite (IHt2 x b).
reflexivity.
apply (lt_D_bsize b x0 x1 x2).
rewrite H3 in H.
trivial.
Qed.



Lemma elmnt_lkp_upd : forall (t:BTree) (i j:BN), i <BN (bsize t) -> j <BN (bsize t) -> i <> j -> forall (x:A), lookup_bn (update t i x) j = lookup_bn t j.
Proof.
intros t.
induction t.
(* t = E*)
intros.
simpl in H0.
inversion H0.
(* t = N a t1 t2 *)
intros.
assert (tBal:=allBal (N a t1 t2)).
destruct (bbal_inv (N a t1 t2)).
discriminate.
(* exists z : A, N a t1 t2 = N z E E *)
destruct H2.
inversion H2.
rewrite H5 in H; rewrite H6 in H; simpl in H.
(* inversion  i <BN U Z *)
inversion H.
(* Z = i *)
clear H8 a0.
rewrite H5 in H0; rewrite H6 in H0; simpl in H0.
(* inversion  j <BN U Z *)
inversion H0.
(* Z = j *)
clear H9 a0.
rewrite <- H3 in H1; rewrite <- H7 in H1;intuition.
(* U a0 = j *)
inversion H9.
(* D a0 = j *)
inversion H9.
(* U a0 = i *)
inversion H8.
(* D a0 = i *)
inversion H8.
(*  exists (z : A) (r1 r2 : BTree),
         bbal r1 /\ bbal r2 /\ r1 <> E /\ N a t1 t2 = N z r1 r2 *)
destruct H2; destruct H2; destruct H2.
destruct H2; destruct H3; destruct H4; destruct H5.
destruct i.
(* i = Z *)
destruct j.
(* j = Z *)
intuition.
(* j = U j *)
intuition.
(* j = D j *)
intuition.
(* i = U i *)
destruct j.
(* j = Z *)
intuition.
(* j = U j *)
simpl.
assert (Leq:=bbal_size_l a t1 t2).
assert (Leq1:=Leq).
apply (lt_lteqBN_trans (U i)) in Leq.
apply (lt_lteqBN_trans (U j)) in Leq1.
inversion Leq.
inversion Leq1.
apply (IHt1 i j).
trivial.
trivial.
(*U i <> U j -> i <> j*)
apply U_not.
trivial.
trivial.
trivial.
(* j = D j *)
intuition.
(* i = D i *)
destruct j.
(* j = Z *)
intuition.
(* j = U j *)
intuition.
(* j = D j *)
simpl.
assert (Leq:=bbal_size_r2 a t1 t2).
assert (Leq1:=Leq).
apply (lt_lteqBN_trans (D i)) in Leq.
apply (lt_lteqBN_trans (D j)) in Leq1.
inversion Leq.
inversion Leq1.
apply (IHt2 i j).
trivial.
trivial.
(*D i <> D j -> i <> j*)
apply D_not.
trivial.
trivial.
trivial.
Qed.



(*This property is given in the introduction as an example of why we prefer to use the numeric system BN over nat*)
Lemma lkp_upd_BN: forall (t:BTree) (x:A) (b:BN), t <> E -> b <BN (bsize t) -> lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
(*Induction on t*)
induction t.
(*Base case t = E *)
intuition.
(*Induction step t = N a t1 t2*)
intros.
(*cases on BNat number b*)
destruct b.
(*1. b=Z*)
reflexivity.
(*2. b = U b*)
destruct (eq_btree_dec t1 E).
(*Cases on t1*)
(*i) t1=E A*)
assert (t2 = E).
eapply leftE_leaf.
eexact H.
trivial.
(*t1=E  and t2=E *)
rewrite e in H1.
rewrite H2 in H1.
simpl in H1.
inversion H1.
(*Contradiction: b <BN Z*)
inversion H5.
(*ii) t1<>E A*)
apply IHt1.
inversion H.
trivial.
trivial.
(* As required by the inductive hypothesis, we need to prove that b <BN (bsize t1)*)
apply (lt_U_bsize b a t1 t2).
trivial.
(*3. b = D b*)
destruct (eq_btree_dec t2 E).
(* ==> Cases on t2 <== *)
(*i) t2 = E *)
destruct (rightE a t1 t2).
trivial.
trivial.
(*t1=E and t2=E *)
rewrite e in H1.
rewrite H2 in H1.
simpl in H1.
inversion H1.
(*Contradiction: b <BN Z*)
inversion H5.
(*t1= N aa E E and t2=E *)
rewrite e in H1.
destruct H2.
rewrite H2 in H1.
simpl in H1.
inversion H1.
(*Contradiction: b <BN Z*)
inversion H5.
(* ii) t2<>E A*)
apply IHt2.
inversion H.
trivial.
trivial.
(*We need to prove that b <BN (bsize t2)*)
apply (lt_D_bsize b a t1 t2).
trivial.
Qed.
