From mathcomp Require Import all_ssreflect boolp classical_sets.

Section Image.
  Local Open Scope classical_set_scope.
  Context {aT rT:Type}.

  Implicit Types (A B: set aT) (Y Z: set rT) (f: aT -> rT) (g: rT -> aT).

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

  Goal forall f A B, f @` A `\` f @` B `<=` f @` (A `\` B).
  Proof.
    move => f A B y [[a HAa] Hfay HnB].
    exists a.
    split;[apply HAa|
           move => HBa;apply HnB;exists a].
    apply HBa.
    apply Hfay.
      by apply Hfay.
  Qed.

  Goal forall (T1 T2 T3:Type) (f:T1 -> T2) (g:T2 -> T3), injective f -> injective g -> injective (g \o f).
  Proof.
    move => T1 T2 T3 f g Hf Hg s t Hfg.
    apply: (Hf s t).
    apply: (Hg (f s) (f t)).
    apply: Hfg.
  Qed.


  Goal forall A Y (f:aT -> rT) (g:rT -> aT),
      cancel f g -> injective f /\ g @` setT = setT.
  Proof.
    move => A Y f g Hcancel.
    split.
    move => s t Hf.
    move: (Hcancel s) (Hcancel t) => Hcancels Hcancelt.
    rewrite -Hcancels -Hcancelt Hf.
    reflexivity.
    apply predeqP => a.
    split => H.
    done.
    exists (f a).
    done.
    by rewrite Hcancel.
  Qed.

  Definition surjective (aT rT:Type) (A: set aT) (Y: set rT) (f:aT -> rT) :=
    forall y, y \in Y -> Y = f @` A.

End Image.
