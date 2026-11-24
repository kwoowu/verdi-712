(* A Verdi VWS map keyed by Rocq primitive strings (PrimString.string),
   for VarD's keys. Goes in Verdi's theories/Lib/ next to FMapVeryWeak.v.

   Rocq's PString library already provides an ordered type for primitive
   strings (PString.OT), but its equality is [compare s1 s2 = Eq], while
   VarD's functor requires plain Leibniz equality (@eq). PStringOT below is a
   thin wrapper with eq := @eq, proved from PString.compare_eq. The map
   itself is Rocq's balanced-tree FMapAVL, adapted to Verdi's VWS interface
   with the existing WS_to_VWS functor. *)

From Coq Require Import OrderedType FMapAVL.
From Coq Require PrimString PString.
From Verdi Require Import FMapVeryWeak.

Module PStringOT <: OrderedType.OrderedType
    with Definition t := PrimString.string
    with Definition eq := @eq PrimString.string.

  Definition t := PrimString.string.
  Definition eq := @eq PrimString.string.
  Definition lt := PString.OT.lt.

  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt_trans := PString.OT.lt_trans.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y Hlt Heq.
    apply (PString.OT.lt_not_eq x y Hlt).
    unfold PString.OT.eq. rewrite Heq. apply PString.compare_refl.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match PString.OT.compare x y with
    | OrderedType.LT H => OrderedType.LT H
    | OrderedType.EQ H => OrderedType.EQ (proj1 (PString.compare_eq x y) H)
    | OrderedType.GT H => OrderedType.GT H
    end.

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof.
    destruct (PrimString.compare x y) eqn:H.
    - left. apply PString.compare_eq. exact H.
    - right. intro E. subst. rewrite PString.compare_refl in H. discriminate.
    - right. intro E. subst. rewrite PString.compare_refl in H. discriminate.
  Defined.
End PStringOT.

Module PStringMapAVL := FMapAVL.Make PStringOT.
Module LogTimePStringMap <: VWS := WS_to_VWS PStringMapAVL.