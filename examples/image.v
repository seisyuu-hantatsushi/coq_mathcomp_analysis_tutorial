From mathcomp Require Import all_ssreflect boolp classical_sets.

Section Image.
  Local Open Scope classical_set_scope.
  Context {aT rT:Type}.
  Implicit Types (A B: set aT) (f: aT -> rT) (Y Z: set rT).

  Goal forall f A, A `<=` f @^-1` (f @` A).
  Proof.
    move => f A a HainA.
    unfold preimage.
    unfold mkset.
    unfold image.
    unfold mkset.
    by exists a.
  Qed.

  Goal forall f A, A `<=` f @^-1` (f @` A).
  Proof. by apply preimage_image. Qed.
  
End Image.
