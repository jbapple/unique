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

(*
Lemma eqp : forall (n:nat) m, {n = m} + {n <> m}.
intros.
remember (lt_eq_lt_dec n m) as nm.
destruct nm.
{ 
  destruct s.
  { right. omega. }
  { left; omega. }
}
{
  right; omega.
}
Defined.
*)
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

(*
Fixpoint validSize {a} (x:Braun a) :=
  match x with
    | Tip => true
    | Top ods _ evs => 
      andb (validSize ods) 
           (andb (validSize evs)
                 (let p := size ods in
                  let q := size evs in
                  if eqp p q
                  then true
                  else if eqp p (q+1)
                       then true
                       else false))
  end.
*)

Set Maximal Implicit Insertion.

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

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

Ltac help := 
  repeat 
  match goal with
    | [H : _ /\ _ |- _] => destruct H
    | [|- _ /\ _] => split
    | [H : prod _ _ |- _] => destruct H
    | [H : ?P, G : ?P -> ?Q |- _] => notHyp Q; assert Q; try (exact (G H))
    | _ => simpl in *; intros; auto; try omega
  end.

Unset Ltac Debug.

Lemma pushFrontSize : forall a (xs:Braun a) x, 1 + size xs = size (pushFront x xs).
Proof with help.
induction xs as [|lean ods _ hd evs]...
assert (size (pushFront hd evs) = 1 + size evs)...
Qed.

Lemma pushFrontValid : forall a (xs:Braun a), validSize xs -> forall x, validSize (pushFront x xs).
Proof with help.
induction xs...
(rewrite <- pushFrontSize)...
destruct l...
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
    match popFront xs with
      | None => 0 = size xs
      | Some (_,ys) => size xs = 1 + size ys
    end.
Proof with help.
induction xs...
destruct l; destruct (popFront xs1)...
Qed.

Lemma popFrontValid :
  forall {a} (xs:Braun a),
    validSize xs -> 
    match popFront xs with
      | None => True
      | Some (_,ys) => validSize ys
    end.
Proof with help.
induction xs...
specialize (popFrontSize xs1)...
destruct l; destruct (popFront xs1)...
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

Lemma pushBackSize : forall a (xs:Braun a) x, 1 + size xs = size (pushBack x xs).
Proof with help.
induction xs...
destruct l; help; try (rewrite <- IHxs1); try (rewrite <- IHxs2)...
Qed.

Lemma pushBackValid : forall a (xs:Braun a), validSize xs -> forall x, validSize (pushBack x xs).
Proof with help.
induction xs...
destruct l; help; try (rewrite <- pushBackSize)...
Qed.

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
      let z := fresh in remember x as z; destruct z
    | [H : (_,_) = (_,_) |- _] => inversion H
    | [|- let (_,_) := ?x in _ ] => 
      let z := fresh in remember x as z; destruct z
    | _ => repeat help
  end)).

Lemma pairListLength :
  forall {a} (xs:list a),
    forall p q,
      (p,q) = pairList xs ->
      length xs = length p + length p + (match q with None => 0 | _ => 1 end).
Proof with helper.
assert (forall n, forall {a} (xs:list a), 
          length xs = n ->
          forall p q,
            (p,q) = pairList xs ->
            n = length p + length p + 
                (match q with None => 0 | _ => 1 end)).
{
  eapply (@well_founded_ind 
            _ 
            (fun p q => p < q) 
            lt_wf (fun z => forall {a} (xs:list a), 
                              length xs = z ->
                              forall p q,
                                (p,q) = pairList xs ->
                                z = length p + length p + 
                                    (match q with None => 0 | _ => 1 end)))...
  destruct xs; try (destruct xs)...
  remember (pairList xs) as px; destruct px...
  erewrite H with (y := length xs) (p := l) (q := o)...
}
intros...
eapply H...
Qed.

(*
Lemma pairListLength : 
  forall (n:nat), forall {a} (xs:list a),
    length xs = n -> 
    length (fst (pairList xs)) <= n.
Proof with help.
eapply (@well_founded_ind _ (fun p q => p < q) _ (fun z => forall a (xs:list a), length xs = z -> length (fst (pairList xs)) <= z)).
intros.
destruct xs.
help.
destruct xs.
help.
simpl.
help.
remember (pairList xs) as px.
destruct px.
help.
assert (l = fst (pairList xs)); help.
rewrite <- Heqpx. help.
rewrite H1.
assert (length (fst (pairList xs)) <= length xs).
eapply H; help.
help.
Grab Existential Variables.
apply well_founded_ltof.
Qed.
*)

Fixpoint unpairBraun {a} (xs: Braun (a*a)) : (Braun a*Braun a):=
  match xs with
    | Tip => (Tip,Tip)
    | Top lean ods (hd1,hd2) evs =>
      let (ods1,ods2) := unpairBraun ods in
      let (evs1,evs2) := unpairBraun evs in
      (Top lean ods1 hd1 evs1, Top lean ods2 hd2 evs2)
  end.

(*
braunMap 

Lemma braunProp : forall P xs, (forall f, P (braunMap f xs)) -> forall q r, (q,r) = unpairBraun xs -> P q /\ P r.
*)

Require Import Recdef.

(*
Fixpoint braunKids (n:nat) : prod nat nat :=
  match n with
    | 0 => (0,0)
    | 1 => (1,0)
    | S (S m) =>
      let (p,q) := braunKids m
      in (S p, S q)
  end.
*)
Fixpoint half (n:nat) : nat :=
  match n with 
    | S (S m) => S (half m)
    | _ => 0
  end.


Lemma halfDecreasing : forall n , half n < S n /\ half (S n) < S n.
intros.
induction n.
help.
help.
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
help...
clear.
unfold id.
eapply (halfDecreasing m).
Qed.

Check fromListHelp_equation.


Functional Scheme fromListHelp_ind := Induction for fromListHelp Sort Prop.
Check fromListHelp_ind.

Definition fromList {a} (xs:list a) :=
  fromListHelp (length xs) _ xs.

Lemma unpairBraunSize : 
  forall a (xs:Braun (a*a)), 
    let (p,q) := unpairBraun xs in 
    size p = size xs /\ size q = size xs.
Proof with help.
induction xs...
destruct (unpairBraun xs1);
  destruct (unpairBraun xs2)...
Qed.

(*
Ltac helper := help; repeat (subst;
  match goal with
    | [_ : let (_,_) := ?x in _ |- _] => 
      let z := fresh in remember x as z; destruct z
    | [H : (_,_) = (_,_) |- _] => inversion H
    | [|- let (_,_) := ?x in _ ] => 
      let z := fresh in remember x as z; destruct z
    | _ => repeat help
  end).
*)
Lemma unpairBraunValid : 
  forall a (xs:Braun (a*a)), 
    let (p,q) := unpairBraun xs in 
    validSize xs -> validSize p /\ validSize q.
Proof with helper.
Print validSize.
Set Ltac Debug.
Unset Ltac Debug.
induction xs...
pose (unpairBraunSize _ xs1).
pose (unpairBraunSize _ xs2).
rewrite <- HeqH0 in *.
rewrite <- HeqH in *.
destruct l...
pose (unpairBraunSize _ xs1).
pose (unpairBraunSize _ xs2).
rewrite <- HeqH0 in *.
rewrite <- HeqH in *.
destruct l...
Qed.


Lemma halfPlus : forall n, half n + half n <= n /\ half (S n) + half (S n) <= S n.
Proof with help.
induction n...
Qed.

Lemma pairListHalf : forall a (xs:list a), length (fst (pairList xs)) = half (length xs) 
                                           /\ forall x, length (fst (pairList (x :: xs))) = half (length (x :: xs)).
Proof with helper.
induction xs...
remember (pairList xs) as px; destruct px...
Qed.

Lemma fromListHelpSize : forall a (xs:list a), 
                           size (fromListHelp (length xs) a xs) = length xs.
Proof with help.
assert (forall n, forall a (xs:list a), n = length xs ->
          size (fromListHelp n a xs) = n).
{
  eapply (@well_founded_ind _ (fun p q => p < q) lt_wf 
                            (fun z => forall a (xs:list a), 
                                        z = length xs ->
                                        size (fromListHelp z a xs) = z)).
  intros...
  destruct xs.
  {
    help.
    rewrite fromListHelp_equation...
    subst...
  }
  {
    rewrite fromListHelp_equation...
    subst...
    remember (pairList xs) as px; destruct px...
    assert (size (fromListHelp (length l) (a * a) l) = length l)...
    {
      eapply H...
      Check pairListLength.
      assert (length xs >= length l + length l)...
      assert (length xs = 2*(length l) \/ length xs = 2*(length l) + 1)...
      pose (pairListLength xs l o)...
      rewrite H0...
      destruct o...
    }
    assert (half (length xs) = length l).
    {
      pose (pairListHalf _ xs)...
      rewrite <- Heqpx in * ...
    }
    rewrite H1...
    remember (unpairBraun (fromListHelp (length l) (a * a) l)) as up; destruct up as [evs ods]...
    assert (size evs = length l /\ size ods = length l); 
      pose (unpairBraunSize _ (fromListHelp (length l) (a * a) l))...
    rewrite <- Hequp in * ...
    rewrite <- Hequp in * ...
    pose (pairListLength xs l o)...
    destruct o...
    rewrite <- pushBackSize...
  }
}
intros...
Qed.

Lemma fromListHelpValid : forall a (xs:list a), 
                           validSize (fromListHelp (length xs) a xs).
Proof with helper.
assert (forall n, forall a (xs:list a), n = length xs ->  
                           validSize (fromListHelp (length xs) a xs)).
(*
Intuitively, apply well-founded induction to prove the recursive call 
produces a validSezed tree, then call  fromListHelpSize on the results.
 *)
{
  eapply (@well_founded_ind _ (fun p q => p < q) lt_wf 
                            (fun z => 
                               forall a (xs:list a), 
                                 z = length xs ->  
                                 validSize (fromListHelp (length xs) a xs)))...
  (* Again, we need to get to the non-nill case to find the recursive call *)
  destruct xs...
  {
    rewrite fromListHelp_equation...
  }
  {
    rewrite fromListHelp_equation...
    remember (pairList xs) as px; destruct px...
    (* Now the inductive call *)
    assert (validSize (fromListHelp (length l) (a * a) l))...
    {
      eapply (@H (length l))...
      assert (length xs >= length l + length l)...
      assert (length xs = 2*(length l) \/ length xs = 2*(length l) + 1)...
      pose (pairListLength xs l o)...
      rewrite H0...
      destruct o...
    }
    assert (half (length xs) = length l).
    {
      pose (pairListHalf _ xs)...
      rewrite <- Heqpx in * ...
    }
    rewrite H1...
    remember (unpairBraun (fromListHelp (length l) (a * a) l)) as up; destruct up as [evs ods]...
    (* Now we need to know that evs and ods are validSized *)
    pose (fromListHelp (length l) (a * a) l) as recur...
    fold recur in Hequp...
    fold recur in H0...
    pose (unpairBraunValid _ recur).
    rewrite <- Hequp in * ...
    destruct o...
    {
      apply (pushBackValid)...
    }
    {
      rewrite <- (pushBackSize)...
      assert (size evs = size ods)...
      {
        pose (unpairBraunSize _ recur)...
        rewrite <- Hequp in * ...
      }
    }
    {
      pose (unpairBraunSize _ recur)...
      rewrite <- Hequp in * ...
    }
  }
}
intros...
specialize (H (length xs))...
Qed.

Fixpoint toList {a} (xs:Braun a) :=
  match xs with
    | Tip => nil
    | Top lean ods hd evs =>
      let (both,rest) := pairUp ods evs in
      appendOpt (cons hd (flatten both)) rest