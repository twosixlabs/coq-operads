Require Import List.
Require Import Nat. 
Import ListNotations.

(*GENERAL Definitions we need*)
(*These appply to all types A, and we will specialize to our specific type T later on*)

(*replaces the ith entry of an old list with a new list*)
Definition insert{A : Type} (i:nat) (old new : list A) : list A := 
  firstn i old ++ new ++ skipn (i+ 1) old. 

(*returns the ith entry of a list, and returns a default element otherwise*)
Definition lookup {A:Type}{def:A} (i: nat)(xs : list A)  : A := 
  nth i xs def.

(*defines the composition of two functions*)
Definition comp {A B C} (g : B -> C) (f : A -> B) := 
  fun x : A => g (f x).

(*defining when two morphisms between types are inverse to one another*) 
Definition inv {X Y: Type}(f: X-> Y)(g: Y -> X) : Prop := 
  comp f g = id /\ comp g f = id.

(*defining when two types are isomorphic, want to use this in T*) 
Definition iso (X Y : Type) : Prop := 
  exists (f: X-> Y)(g:Y->X), inv f g. 

(*------------------------------------------------------------------------------------------*)
(*Setting up T and Definitions for T. This correspnods to creating the 
the collection T to be used in the operad Sets_T *)

(*This is our collection of types that will help form the basis of our collection T*) 
(*currently we only have three types: n, b, and u*)
Inductive baseTypes : Type := 𝕟 | 𝕓 | 𝕦.

(*this assigns a value of a type within T to a value in Coq *)
(*e.g. it interprets the symbol in our collection of symbols in BaseTypes*)
Definition interpT (ty: baseTypes) : Type :=
  match ty with
  | 𝕦 => unit
  | 𝕟 => nat
  | 𝕓 => bool
 end.    

(*This is the inductive definition of our collection of types T*)
(*this definition assigns our baseTypes part of our Type T
and also allows us to define operation types on our BaseTypes, such as product (this is 'p') and 
function (this is 'fn') *)
(*these are all the operations we would have *)
Inductive T : Type :=
  | Ty : baseTypes -> T
  | p : T -> T  -> T
  | fn : T -> T  -> T.

(*this assigns value in Coq to anything within our type T*)
Fixpoint El (ty : T) : Type :=
  match ty with
  | (Ty t) => interpT t
  | (p A B) => prod (El A) (El B) 
  | (fn A B) => El A -> El B
  end. 

(*Notation for anything within T*)
Notation "A → B" := (fn A B) (at level 20). (* \-> *)
Notation "| T |" := (Ty T) (at level 25). 
Notation "A ⊗ B" := (p A B) (at level 23). (* \otimes *)

(*Example using insert and types formed from T*)
Example insertEx : 
  insert 2  [|𝕦|; |𝕟|; |𝕟|⊗ |𝕓|; |𝕦|→|𝕟| ] [|𝕟|; |𝕓|] = [|𝕦|; |𝕟|; |𝕟|; |𝕓|; |𝕦|→|𝕟| ]. 
Proof. 
  compute. reflexivity. 
Qed. 

(*returns the ith element of a list of type T*)
(*if it is out of range, it returns unit, which is the 
  type of a single element set in T*) 
Definition lookupT (i: nat)(xs: list T) : T := 
  @lookup T (|𝕦|) i xs . 

(*example of lookupT*)
Example lookupEx : 
 lookupT 2 [|𝕦|; |𝕟|; |𝕟|⊗ |𝕓|; |𝕦|→|𝕟| ] = |𝕟|⊗ |𝕓|. 
Proof. 
 compute. reflexivity. 
Qed.  

(* ---------------------------------- *)
