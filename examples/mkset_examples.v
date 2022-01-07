From mathcomp Require Import all_ssreflect boolp classical_sets.

Section Classical_Sets_Examples.
  Local Open Scope classical_set_scope. 

  Variable T:Type.

  Inductive Fruits : Type :=
  | Apple
  | Orange
  | PineApple
  | Mango.

  Definition IsMyFruits (fruits : Fruits) : Prop :=
    match fruits with
    | Apple => True
    | Orange => True
    | Mango => True
    | _ => False
    end.

  Print mkset.
  Definition MyFruits : set Fruits := mkset IsMyFruits.

  Goal Apple \in MyFruits.
  Proof.
    rewrite in_setE.
    unfold mkset.
    unfold MyFruits.
    rewrite mksetE.
    done.
  Qed.

  Goal PineApple \in ~`MyFruits.
  Proof.
    unfold setC.
    rewrite in_setE.
    rewrite mksetE.
    unfold MyFruits.
    rewrite mksetE.
    done.
  Qed.

  Print nat.

  Fixpoint IsEven(n : nat) : Prop :=
    match n with
    | O => True
    | S O => False
    | S (S n') => IsEven n'
    end.

  Goal 2 \in mkset IsEven.
  Proof.
    rewrite in_setE.
    unfold mkset.
    unfold IsEven.
    done.
  Qed.

  Goal 3 \notin mkset IsEven.
  Proof.
    rewrite notin_set.
    unfold mkset.
    unfold IsEven.
    apply.
  Qed.

End Classical_Sets_Examples.
