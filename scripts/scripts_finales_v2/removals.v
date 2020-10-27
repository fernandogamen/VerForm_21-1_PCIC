Load extensions.


(* Load defBTree. *)

(* Low remove *)

Fixpoint lr (t:BTree) : BTree  :=
 match t with
  |E => undefBTree 
  |N x l r => match bsize l with
               | Z => E
               | _ => N (lookup_bn l Z) r (lr l)
              end
(*  |N x E E => E
  |N x E t2 => undefBTree  
  |N x t1 t2 => N (lookup_bn t1 Z) t2 (lr t1) *)
 end.

Lemma lr_nonE: forall (t1 t2:BTree) (a:A), t1 <> E -> lr (N a t1 t2) = N (lookup_bn t1 Z) t2 (lr t1).
Proof.
intros.
assert (bsize t1 <> Z).
apply bsize_nonZ.
trivial.
simpl.
destruct (bsize t1).
intuition.
trivial.
trivial.
Qed.


Lemma bsize_lr: forall (t:BTree), bbal t -> t <> E  -> bsize (lr t) = predBN (bsize t).
Proof.
intros.
assert (B:=H).
induction H.
contradict H0.
reflexivity.
(* apply bbal_inv2 in H0 *)
apply bbal_inv in H0.
destruct H0.
destruct H0 as [z H0].
rewrite H0.
simpl.
reflexivity.
destruct H0 as [z H0].
destruct H0 as [t1 H0].
destruct H0 as [t2 H0].
destruct H0.
destruct H4.
destruct H5.
inversion H6.
rewrite lr_nonE.
simpl.
rewrite H9 in IHbbal1.
rewrite IHbbal1.
rewrite predsucBNinv.
rewrite plusSuc_2.
rewrite sucpredBNinv.
apply plusComm.
apply bsize_nonZ.
trivial.
trivial.
trivial.
trivial.
Qed.


Lemma bal_lr: forall (t:BTree), bbal t -> t <> E -> bbal (lr t).
Proof.
intros.
induction H.
intuition.
apply bbal_inv in H0.
destruct H0.
destruct H0.
rewrite H0.
simpl.
constructor.
destruct H0 as [z H0].
destruct H0 as [r1 H0].
destruct H0 as [r2 H0].
destruct H0.
destruct H4.
destruct H5.
rewrite lr_nonE.
inversion H6.
constructor.
trivial.
rewrite H9 in IHbbal1. 
exact (IHbbal1 H5).
rewrite bsize_lr.
rewrite H9 in H2.
rewrite H10 in H2.
rewrite H9 in H3.
rewrite H10 in H3.
apply lteqBN_suc_pred.
apply bsize_nonZ in H5.
trivial.
trivial.
trivial.
trivial.
rewrite bsize_lr.
rewrite sucpredBNinv.
rewrite <- H9.
rewrite <- H10.
trivial.
apply bsize_nonZ.
trivial.
trivial.
trivial.
inversion H6.
trivial.
Qed.


Lemma lr_idx: forall (t:BTree),  bbal t -> t <> E ->
forall (j:BN), j <BN (bsize (lr t)) -> lookup_bn (lr t) j  = lookup_bn t (sucBN j).
Proof.
intros t H H0.
induction H.
intuition.
apply bbal_inv in H0.
destruct H0.
destruct H0 as [z H0].
intros.
rewrite H0 in H4.
simpl in H4.
inversion H4.
destruct H0 as [z H0].
destruct H0 as [r1 H0].
destruct H0 as [r2 H0].
destruct H0 as [H0 H5].
destruct H5 as [H5 H6].
destruct H6 as [H6 H7].
rewrite lr_nonE.
intros.
destruct j.
simpl.
trivial.
simpl.
trivial.
simpl.
apply IHbbal1.
inversion H7.
trivial.
assert (D j <BN D (bsize (lr s))).
eapply lt_lteqBN_trans.
eexact H4.
apply bbal_size_r2.
inversion H8.
trivial.
inversion H7.
trivial.
Qed.


(* Next we prove that lr and le are inverses *)

Lemma inverse_lr_le: forall (t:BTree), bbal t -> forall (x:A), lr (le x t) = t.
Proof.
intros t H.
assert (B:=H).
induction H.
intros.
simpl.
trivial.
destruct (bbal_inv (N a s t)).
discriminate.
intros.
destruct H3.
rewrite H3.
simpl.
trivial.
destruct H3 as [z H3].
destruct H3 as [r1 H3].
destruct H3 as [r2 H3].
destruct H3.
destruct H4.
destruct H5.
inversion H6.
rewrite <- H8.
rewrite <- H9.
rewrite <- H10.
rewrite <- H9 in H5.
clear H6 H8 H9 H10 H3 H4.
clear z r1 r2.
intros.
simpl le.
rewrite (lr_nonE (le a t) s x). 
rewrite IHbbal2.
rewrite le_head.
trivial.
trivial.
(* tal vez esta ultima meta deba enunciarse como lema aparte ?? *)
destruct t.
simpl.
discriminate.
simpl.
discriminate.
Qed.


Lemma inverse_le_lr: forall (t:BTree), bbal t -> t <> E -> le (lookup_bn t Z) (lr t) = t.
Proof.
intros t B H.
assert (J:=B).
induction J.
intuition.
destruct (bbal_inv (N a s t)).
trivial.
destruct H2.
rewrite H2.
simpl.
trivial.
destruct H2 as [z H2].
destruct H2 as [r1 H2].
destruct H2 as [r2 H2].
destruct H2.
destruct H3.
destruct H4.
inversion H5.
rewrite <- H7.
rewrite <- H9.
rewrite <- H8.
rewrite <- H8 in H4.
clear H7 H8 H9 H5.
clear H2 H3 z r1 r2.
simpl lookup_bn.
rewrite lr_nonE.
Focus 2.
trivial.
simpl.
rewrite IHJ1.
trivial.
trivial.
trivial.
Qed.


(* High remove *)

Fixpoint hr (t:BTree) : BTree  :=
 match t with
  |E => undefBTree
  |N y l r => match bsize l with  (*corresponde a s no vacio en Hoogerwood*)
               |Z => E
               |_ => match bsize t with
                      |D b => N y (hr l) r  (* primero D para que corresponda
                                                 a Hoog *)
                      |U b => N y l (hr r) (* t es de tamano impar  >= 3 *)
                      |Z => undefBTree
                     end
              end  
 end.

Lemma hrRewU: forall (x:A) (l r:BTree), bbal (N x l r) -> bsize l <> Z -> bsize (N x l r) = U (bsize r) -> hr (N x l r) = N x l (hr r).
Proof.
intros.
apply bnNonZ in H0.
destruct H0.
destruct H0.
simpl.
rewrite H0.
apply size_caseU in H1.
rewrite H0 in H1.
rewrite <- H1.
simpl.
trivial.
apply size_caseU in H1.
rewrite H0 in H1.
simpl.
rewrite H0.
rewrite <- H1.
rewrite plus_U.
trivial.
Qed.


Lemma hrRewD: forall (x:A) (l r:BTree), bbal (N x l r) -> bsize l <> Z -> bsize (N x l r) = D (bsize r) -> hr (N x l r) = N x (hr l) r.
Proof.
intros.
apply bnNonZ in H0.
destruct H0.
destruct H0.
apply size_caseD in H1.
rewrite H0 in H1.
simpl.
rewrite H0.
rewrite plusSuc_2.
rewrite <- H1.
simpl.
trivial.
apply size_caseD in H1.
rewrite H0 in H1.
simpl.
rewrite H0.
rewrite plusSuc_2.
rewrite <- H1.
simpl.
trivial.
Qed.










(*
Lemma predBN_UU: forall (x:BN), D (x ⊞ x) = predBN (U (U x)).
Proof.
intros.
induction x.
simpl.
trivial.
simpl plusBN.
rewrite IHx.
reflexivity.
simpl.
rewrite plus_U.
reflexivity.
Qed.
*)

Lemma leftNonEleaf: forall (x:A) (l r:BTree), bbal (N x l r) -> l <> E -> r = E -> exists (z:A), l = N z E E.
Proof.
intros.
eapply rightE in H1.
destruct H1.
exfalso.
apply H0.
eexact H1.
trivial.
eexact H.
Qed.




Lemma bsize_hr: forall (t:BTree), bbal t -> t <> E  -> bsize (hr t) = predBN (bsize t).
Proof.
intros.
assert (B:=H).
induction H.
intuition.
apply bbal_inv in H0.
destruct H0.
destruct H0 as [z H0].
rewrite H0.
simpl.
trivial.
destruct H0 as [z H0].
destruct H0 as [r1 H0].
destruct H0 as [r2 H0].
destruct H0.
destruct H4.
destruct H5.
inversion H6.
rewrite H9 in IHbbal1.
rewrite H10 in IHbbal2.
rewrite H9 in H2.
rewrite H9 in H3.
rewrite H10 in H2.
rewrite H10 in H3.
clear H H1 H8 H9 H10.
rewrite H6 in B.
destruct (eq_btree_dec r2 E).
apply (leftNonEleaf z r1 r2) in B.
destruct B.
rewrite H.
rewrite e.
simpl.
trivial.
trivial.
trivial.
destruct (bbal_size_r z r1 r2).
(* rewrite H6 in B. *)
(* assert (bsize r1 = bsize r2).
eapply size_caseU.
eexact H.*)
rewrite hrRewU.
Focus 2.
trivial.
Focus 2.
apply bsize_nonZ.
trivial.
Focus 2.
trivial.
simpl.
rewrite IHbbal2.
rewrite predsucBNinv.
rewrite plusSuc_2.
rewrite sucpredBNinv.
trivial.
apply bsize_nonZ.
trivial.
trivial.
trivial.
rewrite hrRewD.
Focus 3.
apply bsize_nonZ.
trivial.
Focus 2.
trivial.
simpl.
rewrite IHbbal1.
rewrite predsucBNinv.
rewrite plusSuc.
rewrite sucpredBNinv.
trivial.
apply bsize_nonZ.
trivial.
trivial.
trivial.
trivial.
Qed.


Lemma bal_hr: forall (t:BTree), t <> E -> bbal t -> bbal (hr t).
Proof.
intros t H B.
assert (B2:=B).
induction B.
intuition.
apply bbal_inv in H.
destruct H.
destruct H as [z H].
rewrite H.
simpl.
constructor.
destruct H as [z H].
destruct H as [r1 H].
destruct H as [r2 H].
destruct H as [C1 C2].
destruct C2 as [C2 C3].
destruct C3 as [C3 C4].
inversion C4.
rewrite <- H3.
rewrite <- H4.
rewrite <- H3 in C3.
rewrite H2 in B2.
clear C1 C2 H2 H3 H4.
Check bbal_size_r.
destruct (bbal_size_r z s t).
rewrite hrRewU.
assert (S1:=H).
apply size_caseU in S1.
destruct (eq_btree_dec t E).
rewrite e in S1.
simpl in S1.
apply bsize_nonZ in C3.
rewrite S1 in C3.
intuition.
assert (T:=n).
apply IHB2 in n.
constructor.
trivial.
trivial.
rewrite bsize_hr.
rewrite S1.
constructor 2.
apply ltpred.
apply bsize_nonZ in C3.
rewrite S1 in C3.
trivial.
trivial.
trivial.
rewrite bsize_hr.
rewrite sucpredBNinv.
rewrite S1.
constructor 1.
apply bsize_nonZ.
trivial.
trivial.
trivial.
trivial.
trivial.
apply bsize_nonZ.
trivial.
trivial.
rewrite hrRewD.
assert (H2:=H).
apply size_caseD in H2.
assert (C5:=C3).
apply bsize_nonZ in C5.
assert (C6:=C3).
apply IHB1 in C6.
constructor.
trivial.
trivial.
rewrite bsize_hr.
rewrite H2.
rewrite predsucBNinv.
constructor.
trivial.
trivial.
rewrite bsize_hr.
rewrite <- H2.
constructor 2.
apply ltpred.
trivial.
trivial.
trivial.
trivial.
trivial.
apply bsize_nonZ.
trivial.
trivial.
Qed.


Lemma hr_idx: forall (t:BTree),  bbal t -> t <> E ->
forall (j:BN), j <BN (bsize (hr t)) -> lookup_bn (hr t) j  = lookup_bn t j.
Proof.
intros t H H0.
assert (B:=H).
induction H.
intuition.

apply bbal_inv in H0.
destruct H0.
destruct H0 as [z H0].
intros.
rewrite H0 in H4.
simpl in H4.
inversion H4.
destruct H0 as [z H0].
destruct H0 as [r1 H0].
destruct H0 as [r2 H0].
destruct H0 as [H0 H5].
destruct H5 as [H5 H6].
destruct H6 as [H6 H7].
inversion H7.
rewrite H9 in IHbbal1.
rewrite H10 in IHbbal2.
rewrite H10 in H2.
rewrite H10 in H3.
rewrite H9 in H2.
rewrite H9 in H3.
rewrite H9 in B.
rewrite H10 in B.
rewrite H8 in B.
clear H H1.
clear H8 H9 H10.
assert (bsize r1 <> Z).
apply bsize_nonZ.
trivial.
destruct (bbal_size_r z r1 r2).
rewrite hrRewU.
intros.
destruct j.
simpl.
trivial.
simpl.
trivial.
simpl.
destruct (eq_btree_dec r2 E).
rewrite e in H1.
simpl in H1.
apply leftNonEleaf in B.
destruct B.
rewrite H8 in H1.
simpl in H1.
inversion H1.
trivial.
trivial.
apply IHbbal2.
trivial.
trivial.
rewrite bsize_hr.
simpl in H4.
rewrite bsize_hr in H4.
assert (bsize r1 = bsize r2).
eapply size_caseU.
eexact H1.
rewrite H8 in H4.
rewrite <- (sucpredBNinv (bsize r2))in H4 at 1.
rewrite plus_D in H4.
inversion H4.
trivial.
apply bsize_nonZ.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
trivial.
intros.
rewrite hrRewD.
Focus 2.
trivial.
Focus 2.
trivial.
Focus 2.
trivial.
destruct j.
simpl.
trivial.
Focus 2.
simpl.
trivial.
simpl.
apply IHbbal1.
trivial.
trivial.
rewrite bsize_hr in H4.
rewrite H1 in H4.
simpl in H4.
apply size_caseD in H1.
rewrite bsize_hr.
rewrite H1.
rewrite predsucBNinv.
inversion H4.
trivial.
trivial.
trivial.
trivial.
discriminate.
Qed.



Lemma inverse_hr_he: forall (t:BTree), bbal t -> forall (x:A), hr (he x t) = t.
Proof.
intros t H.
assert (B:=H).
induction H.
intros.
simpl.
trivial.
intros.
destruct (bbal_inv (N a s t)).
discriminate.
destruct H3.
rewrite H3.
simpl.
trivial.
destruct H3 as [z H3].
destruct H3 as [r1 H3].
destruct H3 as [r2 H3].
destruct H3 as [H3 H4].
destruct H4 as [H4 H5].
destruct H5 as [H5 H6].
inversion H6.
rewrite <- H9 in H5.
rewrite <- H9.
rewrite <- H10.
rewrite <- H8.
clear H6 H8 H9 H10.
clear z r1 r2 H3 H4.
Check bbal_size_r.
destruct ( bbal_size_r a s t).
assert (bsize s = bsize t).
eapply size_caseU.
eexact H3.
simpl he.
replace (sucBN (bsize s ⊞ bsize t)) with (U (bsize t)).
cut (bsize (N a (he x s) t) = D (bsize t)).
intros.
rewrite hrRewD.
rewrite IHbbal1.
trivial.
trivial.
constructor.
apply bal_he.
trivial.
trivial.
rewrite bsize_he.
rewrite H4.
constructor.
apply lts.
rewrite bsize_he.
rewrite H4.
constructor.
rewrite bsize_he.
unfold not.
intros.
symmetry in H7.
apply ZnotSucBN in H7.
trivial.
trivial.
simpl.
rewrite bsize_he.
rewrite H4.
apply plus_D.
assert (bsize s = sucBN (bsize t)).
eapply size_caseD.
eexact H3.
simpl he.
replace (sucBN (bsize s ⊞ bsize t)) with (D (bsize t)).
cut (bsize (N a s (he x t)) = U (sucBN (bsize t))).
intros.
rewrite hrRewU.
simpl.
rewrite
IHbbal2.
trivial.
trivial.
constructor.
trivial.
apply bal_he.
trivial.
rewrite bsize_he.
rewrite <- H4.
constructor.
rewrite bsize_he.
rewrite <- H4.
constructor.
apply lts.
apply bsize_nonZ.
trivial.
rewrite bsize_he.
trivial.
simpl.
rewrite bsize_he.
rewrite <- H4.
rewrite plus_U.
trivial.
Qed.



Lemma inverse_he_hr: forall (t:BTree), bbal t -> t <> E -> he (lookup_bn t (predBN (bsize t))) (hr t) = t.
Proof.
intros t H J.
assert (B:=H).
induction H.
intuition.
destruct (bbal_inv (N a s t)).
trivial.
destruct H3 as [z H4].
rewrite H4.
simpl.
trivial.
destruct H3 as [z H4].
destruct H4 as [r1 H4].
destruct H4 as [r2 H4].
destruct H4.
destruct H4.
destruct H5.
inversion H6.
rewrite <- H10.
rewrite <- H9.
rewrite <- H8.
rewrite <- H9 in H5.
clear H8 H9 H10 H3 H4.
destruct (eq_btree_dec t E).
apply leftNonEleaf in B.
destruct B.
rewrite H3.
rewrite e.
simpl.
trivial.
trivial.
trivial.
destruct (bbal_size_r a s t).
(*assert (bsize s = bsize t).
eapply size_caseU.
eexact H3.*)
rewrite H3.
replace (predBN (U (bsize t))) with (D (predBN (bsize t))).
Focus 2.
symmetry.
apply predBNUD.
apply bsize_nonZ.
trivial.
rewrite hrRewU.
simpl.
rewrite bsize_hr.
replace (sucBN (bsize s ⊞ predBN (bsize t))) with (D (predBN (bsize t))).
rewrite IHbbal2.
trivial.
trivial.
trivial.
assert (bsize s = bsize t).
eapply size_caseU.
eexact H3.
rewrite H4.
rewrite <- (sucpredBNinv (bsize t)) at 2.
rewrite plus_D.
trivial.
apply bsize_nonZ.
trivial.
trivial.
trivial.
trivial.
apply bsize_nonZ.
trivial.
trivial.
assert (bsize s = sucBN (bsize t)).
eapply size_caseD.
eexact H3.
rewrite hrRewD.
Focus 4.
trivial.
Focus 3.
apply bsize_nonZ.
trivial.
Focus 2.
trivial.
rewrite H3.
change (predBN (D (bsize t))) with (U (bsize t)).
simpl.
rewrite bsize_hr.
replace (sucBN (predBN (bsize s) ⊞ bsize t)) with (U (bsize t)).
replace (bsize t) with (predBN (bsize s)).
rewrite IHbbal1.
trivial.
trivial.
trivial.
apply SucBNinj.
rewrite sucpredBNinv.
trivial.
apply bsize_nonZ.
trivial.

rewrite H4.
rewrite predsucBNinv.
rewrite plus_U.
trivial.
trivial.
trivial.
Qed.


(*
Lemma bbal_inv_2: forall (t:BTree), bbal t -> t=E \/  
                          (exists (z:A), t = N z E E)  \/ 
                           exists (z:A) (r1 r2:BTree), r1 <> E /\  t = N z r1 r2.
Proof.
intros.
*)
