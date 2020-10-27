Load braunT_bn.

(* Okasaki's effective functions to compute the size of a Braun tree *)

(*This function returns Z if left and right subtrees have the same size, 
(U Z) if left subtree is larger by one than right subtree, and 'undefBN' if there is an error*)

Fixpoint diff (t:BTree) (b: BN) : BN :=
 match t,b with
  | E, Z => Z
  | E, _ => undefBN (*This case is not present in Okasaki's paper. It shouldn't happen*)
  | N x E E, Z => U Z
  | N x s t, U k => diff s k
  | N x s t, D k => diff t k 
  | N x s t, _ => undefBN (*This case is not present in Okasaki's paper. It shouldn't happen*)
 end.

(* The efficient function that computes the size
of a Braun tree according to the Okasaki's paper*)
Fixpoint oksize (t:BTree) : BN :=
 match t with
  | E => Z
  | N x s t => (U(oksize t) ⊞ diff s (oksize t))
 end.

Lemma simpl_diff1: forall (a:A) (t1 t2: BTree) (b:BN),  diff (N a t1 t2) (U b) = diff t1 b.
Proof.
intros.
destruct t1.
destruct t2.
trivial.
trivial.
trivial.
Qed.

Lemma simpl_diff2: forall (a:A) (t1 t2: BTree) (b:BN),  diff (N a t1 t2) (D b) = diff t2 b.
Proof.
intros.
simpl.
destruct t1.
destruct t2.
reflexivity.
reflexivity.
reflexivity.
Qed.

Lemma leaf_bsize:forall (t:BTree) (a:A), bbal(N a t E) -> bsize(N a t E)= U Z -> t=E.
Proof.
intros.
apply rightE in H.
destruct H.
trivial.
destruct H.
rewrite H in H0.
simpl in H0.
inversion H0.
trivial.
Qed.

Lemma bbal_t2_u2: forall (a a0 a1:A) (t1 t2 u1 u2:BTree), bbal (N a0 (N a1 t1 t2) (N a u1 u2)) -> bbal(N a t2 u2).
Proof.
intros.
inversion H.
clear a2 s t H0 H1 H2.
assert (bsize (N a1 t1 t2) = U (bsize t2) \/ bsize (N a1 t1 t2) = D (bsize t2)).
apply bbal_size_r.
assert (bsize (N a u1 u2) = U (bsize u2) \/ bsize (N a u1 u2) = D (bsize u2)).
apply bbal_size_r.
inversion H3.
clear a2 s t H9 H11 H12 H2 H7 H8.
inversion H4.
clear a2 s t H9 H12 H13 H2 H7 H8.
destruct H0.
(* bsize (N a0 t1 t2) = U (bsize t2) *)
destruct H1.
(* bsize (N a u1 u2) = U (bsize u2) *)
rewrite H0 in H5; rewrite H0 in H6.
rewrite H1 in H5; rewrite H1 in H6.
apply lteqBN_U_U in H5.
simpl in H6.
apply lteqBN_U_D in H6.
assert ((bsize u2) ≤BN (sucBN(bsize u2))).
apply lteqs.
eapply lteqBN_trans with (a:=bsize t2) in H2.
constructor.
trivial.
trivial.
trivial.
trivial.
trivial.
(* bsize (N a u1 u2) = D (bsize u2) *)
rewrite H0 in H5; rewrite H0 in H6.
rewrite H1 in H5; rewrite H1 in H6.
apply lteqBN_D_U in H5.
simpl in H6.
apply lteqBN_U_U in H6.
constructor.
trivial.
trivial.
trivial.
trivial.
(* bsize (N a0 t1 t2) = D (bsize t2) *)
destruct H1.
(* bsize (N a u1 u2) = U (bsize u2) *)
rewrite H0 in H5; rewrite H0 in H6.
rewrite H1 in H5; rewrite H1 in H6.
apply lteqBN_U_D in H5.
simpl in H6.
apply lteqBN_D_D in H6.
assert ((bsize u2) ≤BN (sucBN(bsize u2))).
apply lteqs.
eapply lteqBN_trans with (a:=bsize t2) in H2.
constructor.
trivial.
trivial.
trivial.
trivial.
trivial.
(* bsize (N a u1 u2) = D (bsize u2) *)
rewrite H0 in H5; rewrite H0 in H6.
rewrite H1 in H5; rewrite H1 in H6.
apply lteqBN_D_D in H5.
simpl in H6.
apply lteqBN_D_U in H6.
constructor.
trivial.
trivial.
trivial.
trivial.
Qed.

Lemma bbal_t1_u2: forall (a a0 a1:A) (t1 t2 u1 u2:BTree), bbal (N a0 (N a1 t1 t2) (N a u1 u2)) -> bsize (N a u1 u2) = U (bsize u2) -> bbal(N a t1 u2).
Proof.
intros.
assert (HBal:=H).
apply bbal_t2_u2 in H.
inversion H.
assert (bsize (N a1 t1 t2) = U (bsize t2) \/ bsize (N a1 t1 t2) = D (bsize t2)).
apply bbal_size_r.
destruct H8.
apply size_caseU in H8.
rewrite <-H8 in H6; rewrite <-H8 in H7.
constructor.
inversion HBal.
inversion H12.
trivial.
trivial.
trivial.
trivial.
assert(bsize(N a0 (N a1 t1 t2) (N a u1 u2)) = sucBN (bsize(N a1 t1 t2) ⊞ bsize(N a u1 u2))).
reflexivity.
rewrite H8 in H9; rewrite H0 in H9.
simpl (sucBN (D (bsize t2) ⊞ U (bsize u2))) in H9.
apply size_caseD in H9.
rewrite H8 in H9; rewrite H0 in H9.
simpl in H9.
apply DInj in H9.
apply size_caseD in H8.
rewrite H9 in H8.
constructor.
inversion HBal.
inversion H13.
trivial.
trivial.
assert ((bsize u2) ≤BN (sucBN(bsize t2))).
apply lteqBN_trans with (b:=bsize t2).
trivial.
apply lteqs.
rewrite H9 in H10; rewrite <- H8 in H10.
trivial.
rewrite H8.
constructor.
Qed.

Lemma diffEq_Z: forall (t s:BTree) (a:A), bbal(N a s t) -> bsize s = bsize t-> diff s (bsize t)=Z.
Proof.
intro.
induction t.
(* t = E *)
intros.
simpl in H0.
apply bsize_Z in H0.
rewrite H0.
reflexivity.
(* t = N a t1 t2 *)
intros.
destruct s.
(* s = E *)
apply leftE_leaf in H.
contradict H.
discriminate.
trivial.
(* s = N a1 s1 s2 *)
assert (bsize(N a t1 t2)= U(bsize t2) \/ bsize(N a t1 t2) = D(bsize t2)).
apply bbal_size_r.
destruct H1.
rewrite H1.
rewrite simpl_diff1.
eapply IHt2.
eapply bbal_t1_u2.
eexact H.
trivial.
rewrite H1 in H0.
assert (Size:=H0).
apply size_caseU in H0.
assert (bsize(N a1 s1 s2)= U(bsize s2) \/ bsize(N a1 s1 s2) = D(bsize s2)).
apply bbal_size_r.
destruct H2.
(* bsize (N a1 s1 s2) = U (bsize s2) *)
rewrite H2 in Size.
apply UInj in Size.
rewrite <- H0 in Size.
trivial.
(* bsize (N a1 s1 s2) = D (bsize s2) *)
rewrite H2 in Size.
inversion Size.
(* bsize (N a t1 t2) = D (bsize t2) *)
rewrite H1.
rewrite simpl_diff2.
eapply IHt2.
eapply bbal_t2_u2.
eexact H.
assert (bsize(N a1 s1 s2)= U(bsize s2) \/ bsize(N a1 s1 s2) = D(bsize s2)).
apply bbal_size_r.
destruct H2.
(* bsize (N a1 s1 s2) = U (bsize s2) *)
rewrite H2 in H0.
rewrite H1 in H0.
inversion H0.
(* bsize (N a1 s1 s2) = D (bsize s2) *)
rewrite H2 in H0.
rewrite H1 in H0.
apply DInj in H0.
trivial.
Qed. 


Lemma diffSuc_UZ: forall (t s:BTree) (a:A), bbal(N a s t) -> bsize s = sucBN(bsize t)-> diff s (bsize t)= U Z.
Proof.
intro.
induction t.
(* t = E *)
intros.
simpl in H0.
destruct s.
(* s = E *)
simpl in H0.
inversion H0.
(* s = N a0 s1 s2*)
assert (bsize(N a0 s1 s2)= U(bsize s2) \/ bsize(N a0 s1 s2) = D(bsize s2)).
apply bbal_size_r.
destruct H1.
(* bsize (N a0 s1 s2) = U (bsize s2) *)
rewrite H1 in H0.
apply UInj in H0.
rewrite H0 in H1.
apply bsize_Z in H0.
rewrite H0 in H; rewrite H0 in H1.
apply leaf_bsize in H1.
rewrite H0; rewrite H1.
reflexivity.
inversion H.
trivial.
(* bsize (N a0 s1 s2) = D (bsize s2) *)
rewrite H0 in H1.
inversion H1.
(* t = N a t1 t2 *)
intros.
destruct s.
(* s = E *)
apply leftE_leaf in H.
contradict H.
discriminate.
trivial.
(* s= N a1 s1 s2 *)
assert (bsize(N a t1 t2)= U(bsize t2) \/ bsize(N a t1 t2) = D(bsize t2)).
apply bbal_size_r.
destruct H1.
(* bsize (N a t1 t2) = U (bsize t2) *)
rewrite H1.
rewrite simpl_diff1.
eapply IHt2.
eapply bbal_t1_u2.
eexact H.
trivial.
rewrite H1 in H0; simpl (sucBN (U (bsize t2))) in H0.
assert (Size:=H0).
apply  size_caseD in H0.
assert (bsize(N a1 s1 s2)= U(bsize s2) \/ bsize(N a1 s1 s2) = D(bsize s2)).
apply bbal_size_r.
destruct H2.
(* bsize (N a1 s1 s2) = U (bsize s2) *)
rewrite H2 in Size.
inversion Size.
(* bsize (N a1 s1 s2) = D (bsize s2) *)
rewrite H2 in Size.
apply DInj in Size.
rewrite Size in H0.
trivial.
(* bsize (N a t1 t2) = D (bsize t2) *)
rewrite H1.
rewrite simpl_diff2.
eapply IHt2.
eapply bbal_t2_u2.
eexact H.
rewrite H1 in H0.
simpl (sucBN (D (bsize t2))) in H0.
assert (bsize(N a1 s1 s2)= U(bsize s2) \/ bsize(N a1 s1 s2) = D(bsize s2)).
apply bbal_size_r.
destruct H2.
(* bsize (N a1 s1 s2) = U (bsize s2) *)
rewrite H2 in H0.
apply UInj in H0.
trivial.
(* bsize (N a1 s1 s2) = D (bsize s2) *)
rewrite H2 in H0.
inversion H0.
Qed.

Lemma eq_size : forall (t:BTree), bbal t -> bsize t = oksize t.
Proof.
intros.
induction t.
(*t=E A*)
reflexivity.
(*t=N A a t1 t2*)
assert (oksize (N a t1 t2) = (U(oksize t2) ⊞ diff t1 (oksize t2))).
reflexivity.
assert (bsize t2 = oksize t2).
apply IHt2.
inversion H.
trivial.
destruct (bbal_size_r a t1 t2).
(* bsize (N a t1 t2) = U (bsize t2) *)
assert (U_bsize:=H2).
apply size_caseU in H2.
eapply diffEq_Z in H2.
rewrite <- H1 in H0.
rewrite H2 in H0.
simpl (U (bsize t2) ⊞ Z) in H0.
rewrite H0; rewrite U_bsize.
reflexivity.
eexact H.
(* bsize (N a t1 t2) = D (bsize t2) *)
assert (D_bsize:=H2).
apply size_caseD in H2.
eapply diffSuc_UZ in H2.
rewrite <- H1 in H0.
rewrite H2 in H0.
simpl (U(bsize t2) ⊞ (U Z)) in H0.
rewrite plus_neutro in H0.
rewrite H0; rewrite D_bsize.
reflexivity.
eexact H.
Qed.
