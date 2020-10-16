Require Import List.
Require Import Utf8.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Variable A : Type.

Inductive binTree :=
| empty : binTree
| node : A -> binTree -> binTree -> binTree.

Fixpoint InBT (x:A) (t:binTree) : Prop :=
match t with
| empty => False
| node y l r => x = y ∨ InBT x l ∨ InBT x r
end.

Notation "l1 ++ l2" := (app l1 l2).

Fixpoint flatBT (t:binTree) : list A :=
match t with
| empty => []
| node x l r => cons x (flatBT l++flatBT r)
end.

Proposition InflatBT : ∀ (t : binTree) (x : A), 
InBT x t → In x (flatBT t).
Proof.
induction t.
- intros.
  inversion H.
- intros.
  simpl in H.
  simpl.
  destruct H.
  + left.
    symmetry.
    exact H.
  + destruct H.
    * right.
      apply in_or_app.
      left.
      apply IHt1.
      assumption.
    * right.
      apply in_or_app.
      right.
      apply IHt2.
      assumption.
Qed.