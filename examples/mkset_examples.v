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

  Definition MyFruits : set Fruits := mkset IsMyFruits.

  Goal Apple \in MyFruits.
  Proof.
    rewrite in_setE.
    unfold mkset.
    unfold MyFruits.
    rewrite mksetE.
    done.
  Qed.
  
End.
