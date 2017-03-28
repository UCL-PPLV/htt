From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype.
From mathcomp.ssreflect
Require Import tuple finfun finset.
Require Import pred pcm unionmap heap heaptac domain stmod stsep stlog stlogR. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Section LList.

Variables (T S : Type).
Notation empty := Unit.
Notation map := seq.map.

(* Inductive definition of linked lists *)
Fixpoint llist (p : ptr) {A : Type}  (xs : seq A) := 
  if xs is x :: xt then 
    fun h => exists r h', 
        h = p :-> x \+ (p .+ 1 :-> r \+ h') /\ llist r xt h'
  else fun h => p = null /\ h = empty.

(******************************************************************)
(***********      Facts about linked lists       ******************)
(******************************************************************)

Lemma llist_null {A : Type} (xs : seq A) h : 
         valid h -> llist null xs h -> 
         [/\ xs = [::] & h = empty].
Proof.
case: xs=>[|x xs] D /= H; first by case: H.
by case: H D=>r [h'][->] _.
Qed. 

Lemma llist_pos {A : Type} (xs : seq A) p h : 
        p != null -> llist p xs h -> 
        exists x r h', 
         [/\ xs = x :: behead xs, p :-> x \+ (p .+ 1 :-> r \+ h') = h & 
             llist r (behead xs) h'].
Proof.
case: xs=>[|x xs] /= H []; last by move=>y [h'][->] H1; hhauto.
by move=>E; rewrite E eq_refl in H.
Qed.

(******************************************************************)

(* Some notes:

The problem with HTT proofs is that they are not incremental in the
program construction. Specifically, we first construct the program,
then is WPs are inferred, and the we have to discharge the proof
obligations coming from the weakening (consequence) rule. Ideally,
what we'd like to have is the goal to be refined based on the program
we write... This might require to overhaul the whole structure of the
HTT development in order to implement the reflection between the proof
goals and the syntactic component.  *)

(* Alternatively, we can just try to fiddle with the unification order
of Coq's wildcard mechanism. *)



(* Type of recursive map *)
Definition llist_map_type (f : T -> S) :=
  forall (p : ptr),   
    {xs : seq T}, STsep (fun h => llist p xs h,
                         fun (_ : ans unit) h => llist p (map f xs) h).

Record Result (f : T -> S) p xs : Prop :=
  Res {
      out_heap : heap ;
      _ : llist p (seq.map f xs) out_heap
    }.

Record IfStatement (T : Type) :=
  IfSt {
      cond : bool;
      then_branch : cond -> T;
      else_branch : ~~cond -> T;
    }.

Definition lmap_type f :=
  forall (p : ptr) (h : heap) (xs : seq T)
         (V : valid h) (pre: llist p xs h),
    Result f p xs.

Program Definition llist_map' (f : T -> S) (p : ptr)
        (h : heap) (xs : seq T) (V : valid h) (pre: llist p xs h)
        (* passing a recursive intance *)
        (rec : lmap_type f) :
  IfStatement (Result f p xs)
  (* Reflecting the speculative syntax into the sigma-type value *)
  (* So let's assume, the top-level statement if a conditional *)
  := @IfSt (Result f p xs) _ _ _.

(* Guessing the coniditional *)
Next Obligation.
exact: (p == null).
Defined.

(* Guessing then-branch *)
Next Obligation.
rewrite /llist_map'_obligation_1 in H.
move/eqP: H=>Z; subst p; case: (llist_null V pre)=>Z1 Z2.
by subst xs h; apply: (@Res f null [::] Unit). 
Defined.

Next Obligation.
rewrite /llist_map'_obligation_1 in H.
case/(llist_pos H): pre=>t [nxt][h'][->]Z/=P; subst h.

(* At this point we can just run the recursor, but this would be
   non-productive, so we won't be doing it. *)
(*
apply: (rec p (p :-> t \+ (p .+ 1 :-> nxt \+ h')) (t :: behead xs))=>//=.
by exists nxt, h'.
Defined.
 *)
set h := p :-> t \+ (p .+ 1 :-> nxt \+ h').
(* We now need to read from h *)

(* TODO: implement reflection for reads and writes *)

(* Next Obligation. *)
(* rewrite /llist_map_obligation_1. *)
(* rewrite /llist_map_obligation_2. *)
(* rewrite /llist_map_obligation_3. *)

(* (* Deconstruct the precondition *) *)
(* apply: ghR=>h xs P V. *)

(* (* Use if-rule *) *)
(* case: ifP=>[X|/negbT X]. *)

(* (* 1. p == null ==> The list is empty. *) *)
(* by move/eqP: X=>Z; subst p; case: (llist_null V P)=>->->; heval. *)
  
(* (* 2. p != null => The list is non-empty. *) *)
(* case/(llist_pos X): P=>t [nxt][h'][->]Z/=P; subst h. *)
(* (* Decompose the list predicate *)  *)
(* rewrite joinA joinC in V *; heval. *)
(* apply: (gh_ex (behead xs)). *)
(* by apply: (@val_do _ _ _ h')=>//=_ h2 Q V'; rewrite joinC; *)
(*    exists nxt, h2; rewrite joinA.  *)
(* Qed. *)

End LList.

