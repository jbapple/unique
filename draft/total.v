Require Import Arith.
Require Import Omega.

Set Reversible Pattern Implicit.
Set Maximal Implicit Insertion.

Inductive Lean := Same | Diff.

Inductive Braun a :=
  Tip : Braun a
| Top : Lean -> Braun a -> a -> Braun a -> Braun a.

Arguments Tip [a].
Arguments Top [a] l ods hd evs.

Fixpoint size {a} (x:Braun a) :=
  match x with
    | Tip => 0
    | Top _ ods _ evs => 1 + size ods + size evs
  end.

Fixpoint validSize {a} (x:Braun a) :=
  match x with
    | Tip => True
    | Top lean ods _ evs => 
      (validSize ods) /\
      (validSize evs) /\
      (let p := size ods in
       let q := size evs in
       match lean with
         | Same => p = q
         | Diff => p = q+1
       end)
  end.


Ltac notHyp P :=
  match P with
    | ?H = ?H => fail 1
    | _ =>
      match goal with
        | [ _ : P |- _ ] => fail 2
        | _ =>
          match P with
            | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 3 ]
            | _ => idtac
          end
      end
  end.

Ltac notKnown v :=
  match goal with
    | [ _ : (_,_) = v |- _ ] => fail 1
    | [ _ : v = (_,_) |- _ ] => fail 1
    | _ => idtac
  end.

Ltac clearImpls :=
  repeat (
      match goal with
        | [H: _ -> _ |- _] => clear H
        | _ => idtac
      end).

Require Import Psatz.

Ltac natSolve := try (solve [clearImpls; lia]).

Unset Ltac Debug.

Lemma symmetric : forall {t:Type} {a:t} {b:t} (x:a=b), b=a.
Unset Ltac Debug.
auto.
Qed.

Unset Ltac Debug.

Ltac help := 
  repeat( 
  repeat subst; simpl in *; intros; auto; try (autorewrite with core);
  match goal with
    | [H : Diff = Same |- _] => inversion H
    | [H : Same = Diff |- _] => inversion H
    | [H: Some _ = None |- _] => solve [inversion H]

    | [H:unit |-_] => destruct H
    | [H: Some _ = Some _ |- _] => inversion_clear H

    | [H : _ /\ _ |- _] => destruct H
    | [H : prod _ _ |- _] => destruct H
    | [H: _ = _ |-_] => 
      let t := type of (symmetric H) in
      notHyp t; assert t; try (solve [exact (symmetric H)])

    | [H : ?P, G : ?P -> _ |- _] => 
      let t := type of (G H) in
      notHyp t; assert t; try (solve [exact (G H)])

    | [|- _ /\ _] => split

    | _ => repeat subst; simpl in *; intros; auto; try (autorewrite with core); natSolve
  end).

Ltac clearReflexive :=
  repeat (
      match goal with
        | [H: ?a = ?a |- _] => clear H
        | _ => idtac
      end).

Ltac know t :=
  repeat (
      match goal with
        | [H : _ = t |- _] => rewrite <- H in *; clearReflexive
        | [H : t = _ |- _] => rewrite H in *; clearReflexive
        | _ => clearReflexive
      end).

(*
Braun trees are size-unique - every tre of the same size has the same shape
*)
Lemma unique : forall (xs ys:Braun unit), 
          size xs = size ys ->
          validSize xs ->
          validSize ys ->
          xs = ys.
Proof with help.
(* We proceed by structural induction on xs. *)
induction xs as [|xlean xod ? ? xev]...
{
  (* If xs is Tip, then its size is 0. Therefore, ys's size is 0, and
  ys is also Tip *)
  destruct ys...
}
(* Otherwise xs is Top, and by symmetric reasoning, ys can't be Tip *)
destruct ys as [|ylean yod ? yev]...
assert (size xod = size yod /\ size xev = size yev);
  destruct xlean; destruct ylean...
Qed.

Definition slide x :=
  match x with
    | Same => Diff
    | Diff => Same
  end.

Fixpoint pushFront {a} (x:a) xs :=
  match xs with
    | Tip => Top Same Tip x Tip
    | Top lean ods v evs => Top (slide lean) (pushFront v evs) x ods
  end.

Lemma pushFrontSize : forall a (xs:Braun a) x, size (pushFront x xs) = 1 + size xs.
Proof with help.
induction xs... 
Qed.

Hint Rewrite pushFrontSize.

Lemma pushFrontValid : forall a (xs:Braun a), validSize xs -> forall x, validSize (pushFront x xs).
Proof with help.
induction xs as [|lean]...
destruct lean...
Qed.

Fixpoint popFront {a} (xs:Braun a) :=
  match xs with
    | Tip => None
    | Top lean ods hd evs => 
      Some (hd,
            match popFront ods with
              | None => Tip
              | Some (y,ys) => Top (slide lean) evs y ys
            end)
  end.

Lemma popFrontSize : 
  forall {a} (xs:Braun a),
    validSize xs -> 
    size xs = 
    match popFront xs with
      | None => 0
      | Some (_,ys) => 1 + size ys
    end.
Proof with help.
induction xs as [|lean xod]...
remember (popFront xod) as px; destruct px...
destruct lean...
Qed.


Functional Scheme popFront_ind := Induction for popFront Sort Prop.

Check popFront_ind.

Lemma popFrontValid :
  forall {a} (xs:Braun a),
    validSize xs -> 
    match popFront xs with
      | None => True
      | Some (_,ys) => validSize ys
    end.
Proof with help.
induction xs as [|lean ods]...
pose (@popFrontSize a)...
remember (popFront ods) as p; destruct p...
destruct lean...
Qed.

Fixpoint pushBack {a} (x:a) xs :=
  match xs with
    | Tip => Top Same Tip x Tip
    | Top lean ods hd evs =>
      match lean with
        | Same => Top Diff (pushBack x ods) hd evs
        | Diff => Top Same ods hd (pushBack x evs)
      end
  end.

Lemma pushBackSize : forall a (xs:Braun a) x, size (pushBack x xs) = 1 + size xs.
Proof with help.
induction xs as [|lean]...
Show.
destruct lean...
Qed.

Hint Rewrite pushBackSize.

Lemma pushBackValid : forall a (xs:Braun a), validSize xs -> forall x, validSize (pushBack x xs).
Proof with help.
induction xs as [|lean]...
destruct lean...
Qed.

Hint Resolve pushBackValid.

Fixpoint pairList {a} (xs: list a) :=
  match xs with
    | nil => (nil, None)
    | cons y nil => (nil, Some y)
    | cons p (cons q qs) => 
      let (r,s) := pairList qs
      in (cons (p,q) r, s)
  end.

Ltac helper := repeat (help; repeat (subst;
  match goal with
    | [_ : let (_,_) := ?x in _ |- _] => 
      notKnown x;
(*    idtac "destra"; idtac x; idtac "destrb";*)
    let z := fresh in remember x as z; destruct z; know x
    | [H : (_,_) = (_,_) |- _] => inversion H
    | [|- let (_,_) := ?x in _ ] => 
      notKnown x;
      let z := fresh in remember x as z; destruct z; know x
    | [|- context[let (_,_) := ?x in _] ] => 
      notKnown x;
      let z := fresh in remember x as z; destruct z; know x
    | _ => repeat help
  end)).

Unset Ltac Debug.

Lemma pairListLengthHelp :
  let f := fun {a} (xs:list a) =>
            let (p,q) := pairList xs in
            length xs = length p + length p + (match q with None => 0 | _ => 1 end) in
  forall {a} ys, (f ys /\ forall (y:a), f (cons y ys)).
Proof with helper.
induction ys; unfold f in * ...
Qed.

Lemma pairListLength :
  forall {a} (xs:list a),
    let (p,q) := pairList xs in
    length xs = length p + length p + (match q with None => 0 | _ => 1 end).
Proof with helper.
intros a xs.
pose (pairListLengthHelp xs)...
Qed.

Fixpoint unpairBraun {a} (xs: Braun (a*a)) : (Braun a*Braun a):=
  match xs with
    | Tip => (Tip,Tip)
    | Top lean ods (hd1,hd2) evs =>
      let (ods1,ods2) := unpairBraun ods in
      let (evs1,evs2) := unpairBraun evs in
      (Top lean ods1 hd1 evs1, Top lean ods2 hd2 evs2)
  end.

Require Import Recdef.

Fixpoint half (n:nat) : nat :=
  match n with 
    | S (S m) => S (half m)
    | _ => 0
  end.


Lemma halfDecreasing : forall n , half n < S n /\ half (S n) < S n.
Proof with help.
induction n...
Qed.


Function fromListHelp (n:nat) {a} (xs:list a) {measure id n} : Braun a :=
  match n,xs with
    | 0,_ => Tip
    | _,nil => Tip
    | S m,cons y ys =>
      let (most,last) := pairList ys in
      let (ods,evs) := unpairBraun (@fromListHelp (half m) (prod a a) most) in
      match last with
        | None => Top Same ods y evs
        | Some final => Top Diff (pushBack final ods) y evs
      end
  end.
Proof with help.
unfold id...
pose (halfDecreasing)...
Qed.

Check fromListHelp_equation.
Hint Rewrite fromListHelp_equation.

Functional Scheme fromListHelp_ind := Induction for fromListHelp Sort Prop.
Check fromListHelp_ind.

Definition fromList {a} (xs:list a) :=
  fromListHelp (length xs) _ xs.

Lemma unpairBraunSize : 
  forall {a} (xs:Braun (a*a)), 
    let (p,q) := unpairBraun xs in 
    size p = size xs /\ size q = size xs.
Proof with helper.
induction xs...
Qed.

Definition bothValid {a} (p:Braun a) (q:Braun a) := validSize p /\ validSize q.

Lemma unpairBraunValidHelp : 
  forall {a} (xs:Braun (a*a)), 
    let (p,q) := unpairBraun xs in 
    validSize xs -> bothValid p q.
Proof with helper.
induction xs as [|? ods ? ? evs]...
{ unfold bothValid... }

unfold bothValid in * |- ...

pose (@unpairBraunSize a)...
know (unpairBraun ods); know (unpairBraun evs)...

unfold bothValid; destruct l...
Qed.

Lemma unpairBraunValid : 
  forall {a} (xs:Braun (a*a)), 
    let (p,q) := unpairBraun xs in 
    validSize xs -> validSize p /\ validSize q.
Proof with helper.
intros a xs.
pose (unpairBraunValidHelp xs)...
Qed.


Lemma halfPlus : forall n, half n + half n <= n /\ half (S n) + half (S n) <= S n.
Proof with help.
induction n...
Qed.

Lemma pairListHalf : forall a (xs:list a), length (fst (pairList xs)) = half (length xs) 
                                           /\ forall x, length (fst (pairList (x :: xs))) = half (length (x :: xs)).
Proof with helper.
induction xs...
Qed.

Require Import Coq.Init.Specif.

Definition validTemp {a} k (v:Braun a) :=
  k = size v /\ validSize v.


Lemma fromListValidSizeHelp : forall (axs:{a : Type & list a}), 
                              let a := projT1 axs in
                              let xs:= projT2 axs in
                              validTemp (length xs) (fromList xs).
Proof with helper.
(* Strong induction on the length of the list *)
apply (induction_ltof1 _ (fun bys => @length (projT1 bys) (projT2 bys))); 
  unfold ltof; unfold fromList;
  intros axs; destruct axs as [a xs];
  destruct xs as [|y ys]...
{ unfold validTemp; helper... } (* The base case is trivial *)
(* For the inductive case, the output (cons y ?) *)
assert (exists p, exists q, (p,q) = pairList ys) as Z; eauto.
destruct Z as [p [q]]...
specialize (@H (existT _ _ p))...
Proof with (repeat (know (pairList ys); helper)).
  assert (length p < S (length ys)) as ll...
  {
    pose (pairListLength ys)...
  }
  assert (half (length ys) = length l)...
  {
    pose pairListHalf...
  }
  know (half (length ys)).
  pose (unpairBraunSize (fromListHelp (length l) _ l))...
  know (unpairBraun (fromListHelp (length l) _ l))...
  unfold validTemp in * ...
  {
    pose (pairListLength ys)...
    destruct o...
  }
  {
    pose (unpairBraunValid (fromListHelp (length l) _ l))...
    know (unpairBraun (fromListHelp (length l) _ l))...  
    destruct o...
  }
Qed.


Lemma fromListValidSize : forall a (xs:list a), 
                            length xs = size (fromList xs)
                            /\ validSize (fromList xs).
Proof with helper.
intros a xs.
pose (fromListValidSizeHelp (existT _ _ xs))...
Qed.

idtac
Fixpoint toList {a} (xs:Braun a) :=
  match xs with
    | Tip => nil
    | Top lean ods hd evs =>
      let (both,rest) := pairUp ods evs in
      appendOpt (cons hd (flatten both)) rest