From mathcomp Require Import all_ssreflect boolp classical_sets.

Section Sets_Operator.

  Local Open Scope classical_set_scope.

  Variable T:Type.
 
  Goal forall A B:set T, A `<=` B /\ B `<=` A -> A = B.
  Proof.
    move => A B.
    case => HAinB HBinA.
    rewrite predeqP => x.
    rewrite /iff.
    split;[apply HAinB|apply HBinA].
  Qed.

  Goal forall A B:set T, A `<=` B /\ B `<=` A -> A = B.
  Proof. move => A B. by rewrite seteqP. Qed.

  Section UseImplicit.
    Implicit Types A B C D : set T.

    Goal forall A B C, (A `|` (B `&` C)) = (A `|` B) `&` (A `|` C).
    Proof.
      move => A B C.
      rewrite predeqE => x.
      split.
      move => [HAx|[HBx HC]].
      split;left;done.
      split;right;done.
      move => [[HAx|HBx] [HAx'|HCx]].
      left;done.
      left;done.
      left;done.
      right;done.
    Qed.

    Goal forall A B C, (A `|` (B `&` C)) = (A `|` B) `&` (A `|` C).
    Proof. move => A B C. by rewrite setUIr. Qed.

  End UseImplicit.

End Sets_Operator.
