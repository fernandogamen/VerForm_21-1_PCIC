Require Import Arith.
Require Import ZArith.
Require Import Classical.


Section No_Nat_Between_0_and_1.

Lemma nat_well_ordered:
  forall (P:nat -> Prop),
  (exists n:nat, P n) ->
  (exists m:nat, P m /\ forall k:nat, P k ->  m <= k).
Proof.
intros.
assert (exists! x, P x /\ forall x', P x' -> x <= x') as G.
  apply dec_inh_nat_subset_has_unique_least_element.
  intro n; apply classic.
  assumption.
destruct G as [x G'].
exists x.
apply G'.
Qed.


Ltac well_ordering_principle H := 
apply nat_well_ordered in H; 
  [destruct H as [r J]; 
    destruct J as [H minimal_r]].


Theorem noNatbtw0and1Forward: ~ exists n:nat, 0<n<1. 
Proof.
unfold not.
intro.
well_ordering_principle H.
assert (0 < r*r).
- apply (mult_lt_compat_r 0 r r); intuition.
- assert (r*r < 1*r).
  + apply (mult_lt_compat_r r 1 r) ; intuition.
  + replace (1*r) with r in H1 by auto with arith.
    assert (0< r*r < 1).
    * assert(r*r<1).
      -- apply (lt_trans (r*r) r 1) ; intuition.
      -- intuition.
    * assert (r <= r*r).
      -- apply minimal_r ; assumption.
      -- assert (~ r*r < r).
         ++ apply le_not_lt; assumption.
         ++ contradiction.
Qed.         
         
    (* apply minimal_r in H2.
      apply le_not_lt in H2.
      contradiction. 
Qed.        
*)


Theorem noNatbtw0and1Backward: ~ exists n:nat, 0<n<1. 
Proof.
unfold not.
intro H.
well_ordering_principle H.
absurd (r*r < r).
- apply le_not_lt.
  apply minimal_r.
  split.
  + replace 0 with (0*r) by auto with arith.
    apply mult_lt_compat_r ; intuition.
  + apply lt_trans with r.
    * replace r with (1*r) at 3 by auto with arith.
      apply mult_lt_compat_r ; intuition.
    * intuition.
- replace r with (1*r) at 3 by auto with arith.
      apply mult_lt_compat_r ; intuition.
Qed.

        

Theorem noNatbtw0and1Bidirectional: ~ exists n:nat, 0<n<1. 
Proof.
unfold not.
intro H.
well_ordering_principle H.
destruct H as [r_gt_zero r_lt_one].
assert (r*r < r).
- assert (rr_lt_r:=mult_lt_compat_r r 1 r r_lt_one r_gt_zero).
  replace (1*r) with r in rr_lt_r by auto with arith.
  assumption.
- assert (rr_lt_r:=H).
  contradict H.
  apply le_not_lt.
  assert (J:=mult_lt_compat_r _ _ _  r_gt_zero r_gt_zero).
  simpl in J.
  assert (rr_lt_1 := (lt_trans (r*r) r 1 rr_lt_r r_lt_one)).
  apply minimal_r.
  intuition.
Qed.



Theorem noNatbtw0and1Native : forall n : nat, ~(0 < n < 1).
Proof.
  do 2 intro.
  destruct H.
  inversion H0 ; subst.
  + inversion H.
  + inversion H2. 
Qed. 





End No_Nat_Between_0_and_1.