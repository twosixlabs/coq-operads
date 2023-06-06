Require Import List.
Require Import Nat. 
Import ListNotations.
Require Import Permutation.
Require Import Arith.
From Hammer Require Import Hammer.

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
(*Defining Operads *)

(*Official definition for what O(d, c) represents for an operad O*)
Record Operad: Type :=
{
  interp : forall (d : T)(c : list T), T;
}.

Notation "operad 〘 d , c 〙" := (interp operad d c)  (at level 10).

(* ---------------------------------- *)
(* List equality Theorems for type casting in the definition of an operads *)
(*In order to actually specify the axioms required in the definition of an operad, we need to prove 
several theorems about list equality so that the definition will type check*)

(*********LEMMAS FOR LEFT UNITY AXIOM**************)

(*inserting the list xs into the list [a] at the zeroth position
 returns the list xs*)
Lemma unityLInsert : forall {A : Type} {a : A} (xs : list A),
  insert 0 [a] xs = xs.
Proof.
  intros. 
  unfold insert. simpl. rewrite app_nil_r. reflexivity. 
Qed.

(*the cast for operads for the left unity axiom*)
Definition unityLCast {operad : Operad}{d : T} {c : list T}
(e : El (operad〘d,insert 0 [d] c〙)) : El ( operad〘d,c〙). 
Proof.
  rewrite unityLInsert in e. apply e.  
Defined.

(*********LEMMAS FOR RIGHT UNITY AXIOM**************)
(*our goal in unityRInsert is: if list c has length n and i < n, and the
  ith entry is ci, then inserting ci into the list c returns the list c*)
(*NOTE:  i stands for index since lists in Coq are indexed starting at 0 and up to length (list) -1*)
Lemma unityRInsert: forall {A:Type}{def: A}(c: list A)(ci: A)(n i: nat),
 1 <= n -> i < n -> length c = n ->  @lookup A def i c = ci -> insert i c [ci] = c.
Proof.
  intros A def c ci. 
  induction c as [| c0 c' IH]. 
  -  intros. simpl in H1. symmetry in H1. rewrite H1 in H. inversion H.
  - destruct i as [| i']. 
      + unfold insert. simpl. intros.  rewrite H2. reflexivity. 
      + destruct n as [| n'].  
          * intros. discriminate H1. 
          *  intros H H0 H1. inversion H1.  simpl. unfold insert. simpl. 
             unfold insert in IH. destruct H. 
              inversion H0. inversion H2. assert (i' <  m). sauto use: H0. 
              inversion H1. intros.  f_equal. 
              apply (@IH m i' H H2 H5 H4).
Qed.  

(*the cast for operads for the right unity axiom*)     
Definition unityRCast {operad : Operad}{d ci:T}{c: list T}(n i: nat)(p: lookupT i c = ci)(q0: 1 <= n)
  (q1: i < n)(r: length c = n)(e : El (operad 〘d, insert i c [ci]〙)) : El (operad 〘d, c〙).
Proof. 
  intros. 
  rewrite (@unityRInsert T (|𝕦|) c ci n i q0 q1 r p) in e. apply e. 
Defined.  

(*********LEMMAS FOR VERTICAL ASSOCIATIVITY AXIOM**************)
(*Preliminaries:*)
(*1 <= n, m *)
(*c is a list of length n*)
(*b is a list of length m*)
(*i is the index of an element in the list c*)
(*j is the index of an element in the list b*)
(*firstn k L returns the first k elements of the list L*)
(*skipn k L skips the first k elements of the list L*)

(*All lemmas given by vertHj are helper lemmas for vertInsert*)

(*The first i + j members of the list of length n + m -1,
firstn i c ++ b ++ skipn (i+1) c, are given by appending the first j members of the list b
to the first i members of the list c*)
Lemma vertH1 : forall{A:Type}(n m i j: nat)(b c: list A), 
  i < n -> j < m -> length c = n -> length b = m 
  ->  firstn (i+j) (firstn i c ++ b ++ skipn (i+1) c) = firstn i c ++ firstn j b. 
Proof.
  intros. 
  rewrite app_assoc.  
  assert(firstn (i + j) ((firstn i c ++ b) ++ skipn (i + 1) c) = firstn (i+j) (firstn i c ++ b) ++ 
  firstn (i+j - length(firstn i c ++b)) (skipn (i+1) c)). 
  -  apply (firstn_app (i+j)). 
  - rewrite H3. assert (length (firstn i c ++ b) = i + m). 
      + rewrite app_length. rewrite H2. rewrite firstn_length. rewrite H1. sauto. 
      + rewrite H4. assert (i+j -(i+m) = 0). sauto. rewrite H5. simpl. 
          rewrite app_nil_r. rewrite firstn_app. 
        assert(length (firstn i c) = i). rewrite firstn_length. sauto. 
          rewrite H6. assert (i+j -i = j).  sauto. rewrite H7.  
         rewrite firstn_all2.  
          * reflexivity. 
          * rewrite H6. sauto.   
Qed. 

(*if you skip the first i+j+1 members of the list firstn i c ++ b ++ skipn (i+1) c) 
you get the last n-i-1 members of c appended to the last m-j-1 members of b *)
Lemma vertH2 : forall{A:Type}(n m i j: nat)(b c: list A), 
  i < n -> j < m -> length c = n -> length b = m
  ->  skipn (i + j +1) (firstn i c ++ b ++ skipn (i+1) c) = skipn (j+1) b ++ skipn (i+1) c. 
Proof.
  intros. 
  rewrite app_assoc.  
  rewrite skipn_app.  assert (length (firstn i c ++ b) = i + m). 
  rewrite app_length. rewrite firstn_length. sauto. 
  rewrite H3. assert (i+j+1 - (i+m) = 0). sauto. rewrite H4. simpl. 
  rewrite skipn_app.   assert(length (firstn i c) = i).  rewrite firstn_length. 
  sauto. rewrite H5. assert(i+j +1 - i  = j+1). sauto. rewrite H6. 
  assert( skipn (i+j+1) (firstn i c) = []). apply skipn_all2. rewrite H5. sauto. 
  rewrite H7.  rewrite app_nil_l. reflexivity. 
Qed.   

(*Before we prove the main theorem, let's show an example of the list equality we want*)

Parameter c0 c1 c2 b0 b1 a0 a1   : Set. 

Example vertLHS := 
  insert 1 (insert 0 [c0;c1;c2] [b0;b1]) [a0;a1].

Example vertRHS := 
  insert 0 [c0;c1;c2]  (insert 1 [b0;b1] [a0;a1]). 

Lemma vertEx : 
  vertLHS = vertRHS.
Proof. 
  compute. reflexivity. 
Qed.

(*assuming all preliminaries:  
this list equality is showing that inserting the list b into the list c at position i,
then inserting the list a into this list at position i+jis equivalent to 
inserting the list a into the list b at position j and then inserting 
this list into the list c at position i*)
Theorem vertInsert : forall{A:Type}(n m i j: nat)(a b c: list A), 
  1 <= n -> 1 <= m ->  i < n -> j < m -> length c = n -> 
length b = m -> insert (i+j) (insert i c b) a = insert i c (insert j b a). 
Proof. 
  intros. 
  unfold insert.
  assert (firstn (i+j) (firstn i c ++ b ++ skipn (i + 1) c)  = 
  firstn i c ++ firstn j b). apply (vertH1 n m i j b c). 
  - apply H1. 
  - apply H2. 
  - apply H3. 
  - apply H4.  
  - rewrite H5.   
  assert (skipn (i + j + 1)(firstn i c ++ b ++ skipn (i + 1) c) = 
  skipn (j + 1) b ++ skipn (i+1) c).  apply (vertH2 n m i j b c). 
  + apply H1. 
  + apply H2. 
  + apply H3. 
  + apply H4. 
  + rewrite H6. rewrite <- app_assoc. apply f_equal.
    symmetry. rewrite <- app_assoc.  rewrite <- app_assoc. reflexivity. 
Qed.

(*vertical associativity cast for operads *)
Definition vertCast {operad : Operad} {n m i j : nat}
          {d: T} {a b c : list T} {p0: 1 <= n}{p1 : 1 <= m}{p2: i < n} 
            {p3: j < m} {p4: length c = n}{p5: length b = m} 
          (e : El (operad 〘d, insert (i+j) (insert i  c b) a〙)) : 
          El (operad 〘d, insert i c (insert j b a)〙). 
Proof.
 rewrite (vertInsert n m i j a b c p0 p1 p2 p3 p4 p5) in e. apply e.
Defined.   

(*********LEMMAS FOR HORIZONTAL ASSOCIATIVITY AXIOM**************)

(*Preliminaries:*)
(*2 <= n*)
(* 1 <= m, l *)
(*c is a list of length n*)
(*b is a list of length m*)
(*a is a list of length l*)
(*i, j are indices of an element in the list c and i < j*) 
(*firstn k L returns the first k elements of the list L*)
(*skipn k L skips the first k elements of the list L*)


(*if you skip m elements of a list c, then n elements of the same list c,
it's the same as skipping n +m elements of the same list c*)
Lemma skipn_skipn : forall {A: Type}  (c: list A)(n m: nat),
    skipn n (skipn m c) = skipn (n + m) c.
Proof. 
  intros. 
  generalize dependent c. 
  generalize dependent n. 
  induction m as [| m' IH]. 
  - simpl. intros. rewrite Nat.add_0_r. reflexivity. 
  -  intros. destruct c.  
      + simpl; repeat(rewrite skipn_nil); reflexivity.
      + simpl. rewrite <-  plus_Snm_nSm. 
          rewrite plus_Sn_m. simpl. rewrite IH. reflexivity. 
Qed.

(*any Lemma with name horizHj is a helper lemma for horizInsert*)

(*taking the first l-1+j members of the list firstn i c ++ a ++ skipn (i + 1) c
of length i + l + n-i-1 = n+l-1 returns the list 
firstn i c ++ a ++ skipn (i+1) (firstn j c) because 
1) i + l <= l-1 + j 
2) firstn i c ++ a ++ skipn (i + 1) c is the list firstn i c ++ a ++ [c(i),...,[c(j)]
*)
Lemma horizH1 : forall {A:Type} (n l i j: nat)(a c : list A),
 2 <= n ->  1 <= l ->  i <  j -> j < n -> length c = n -> length a = l -> 
 firstn (l - 1 + j) (firstn i c ++ a ++ skipn (i + 1) c) = 
  firstn i c ++ a ++ skipn (i + 1) (firstn j c).
Proof. 
  intros. 
  rewrite app_assoc. 
  rewrite firstn_app. assert (length (firstn i c ++ a) = i + l). 
  rewrite app_length. rewrite H4. f_equal. rewrite firstn_length. rewrite H3.  sauto.  
  rewrite H5. assert (l-1 + j - ( i + l) = j -  i -1). sauto. rewrite H6.  
  rewrite firstn_skipn_comm. assert (i + 1 + (j - i - 1) =  j). sauto. rewrite H7. 
  rewrite firstn_app. assert (length (firstn i c) = i). rewrite firstn_length. rewrite H3. sauto. 
  rewrite H8. rewrite <- app_assoc.  
  assert (l <= l-1 + j). sauto use: H0.  rewrite firstn_firstn. 
  assert (min (l - 1 + j) i =  i). sauto. rewrite H10.  assert (l <= l-1 +  j -  i). sauto.
  assert (firstn (l - 1 +  j - i) a = a). apply firstn_all2.  rewrite H4. apply H11. 
  rewrite H12. reflexivity. 
Qed.  

(*note in this lemma:  l-1 + j +1 is not necessarily equal to l+j (particularly if l = 0), so we have to be 
careful and showing that they are equal is part of the proof! *)
(*taking the above note into account, essentially: the list
 firstn i c ++ a ++ skipn (i + 1) c has length i + l + n-i -1 = n+l-1 
and i< j, so skipping the first l+j elements skips everything in firstn i c and a,
and then since i < j, i+1 < j+1, so that this is skipn (j+1) (skipn (i+1) c), which is 
skipn (j+1) c *)
Lemma horizH2 : forall {A:Type} (n l i j: nat)(a c : list A),
 2 <= n ->  1 <= l ->  i <  j -> j < n -> length c = n -> length a = l -> 
  skipn (l - 1 + j +1) (firstn i c ++ a ++ skipn (i + 1) c) = 
  skipn (j+1) c. 
Proof.
  intros. 
  rewrite app_assoc. 
  rewrite skipn_app. 
  assert (min i n = i). sauto use: H1, H2.
  assert (length (firstn i c ++ a) = i + l). rewrite app_length. rewrite H4. f_equal. 
  rewrite firstn_length. rewrite H3.  apply H5. 
  rewrite H6.    assert ( l - 1 +  j + 1 = l +  j).  sauto. rewrite H7. 
  rewrite skipn_app.  assert (length (firstn i c ) =  i). rewrite firstn_length. rewrite H3. 
  apply H5. rewrite H8.   assert (l <= l +  j - i ). sauto.
  assert (skipn (l +  j -  i) a = []). apply skipn_all2. rewrite H4. apply H9. rewrite H10. 
  rewrite app_nil_r.  assert (skipn (l + j) (firstn i c) = []). 
  apply skipn_all2. rewrite H8. sauto. rewrite H11. 
  simpl. rewrite skipn_skipn. assert (l + j - (i + l) + (i + 1) = j+1). sauto. rewrite H12. 
  reflexivity. 
Qed. 

(*Now i < j and j < n, so that the the list
firstn j c ++ b ++ skipn (j+1) c) has > i elements, so taking
the first i elements of this list is equivalent to taking i elements of firstn j c,
which is equivalent to taking the first i elements of c, since i < j *)
Lemma horizH3: forall {A:Type} (n m i j : nat)(b c : list A),
   2 <= n ->  1 <= m ->   i <  j -> j < n -> length c = n -> length b = m -> 
  firstn i (firstn j c ++ b ++ skipn (j+1) c) = firstn i c. 
Proof. 
  intros. 
  rewrite app_assoc. 
   rewrite firstn_app. 
  assert (length (firstn j c) =  j). rewrite firstn_length. rewrite H3. sauto. 
  rewrite app_length. rewrite H5. rewrite H4. assert (i - (j + m) = 0). sauto.
  rewrite H6. simpl. rewrite app_nil_r. rewrite firstn_app. rewrite H5. assert (i-j = 0). sauto. 
  rewrite H7. simpl. rewrite app_nil_r. rewrite firstn_firstn. assert (min i j = i). sauto. 
  rewrite H8. reflexivity.     
Qed. 

(*Now i < j, i+1 <= j and j < n, so that the the list 
  firstn j c has at least j elements, so that the list,
firstn j c ++ b ++ skipn (j+1) c, has at least j elements 
so that when we skip the first i+1 of them, we can attain that
by skipping the first i+1 of the list firstn j c and then appending
the list b and then the list skipn (j+1) c*)
Lemma horizH4 :  forall {A:Type} (n m i j : nat)(b c : list A),
   2 <= n ->  1 <= m ->   i <  j -> j < n -> length c = n -> length b = m -> 
  skipn (i+1) (firstn j c ++ b ++ skipn (j+1) c) = 
  skipn (i+1) (firstn j c) ++ b ++ skipn (j+1) c.  
Proof. 
  intros. 
  rewrite app_assoc. rewrite skipn_app.  rewrite app_length. 
  rewrite H4. rewrite firstn_length. rewrite H3. assert (min j n = j). sauto. 
  rewrite H5. assert (i+1 - (j+m) = 0). sauto. rewrite H6. 
  simpl. rewrite skipn_app. rewrite firstn_length. rewrite H3. rewrite H5. 
 assert (i+1 - j = 0). sauto. rewrite H7. simpl.  rewrite <- app_assoc. reflexivity.    
Qed. 

(*Assuming all preliminaries:  
inserting the list a into the list c at position i and then inserting the list b into this new list in
position l-1+j returns the same list as inserting b into c at position j, then 
inserting a into this new list at position j*)
Theorem horizInsert: forall {A:Type}(n m l i j : nat)(a b c : list A),
  2 <= n -> 1 <= m -> 1 <= l -> i <  j -> j < n -> length c = n -> length a = l -> length b = m -> 
   insert (l-1+j) (insert i c a) b = insert i (insert j c b) a.
Proof. 
  intros. 
  unfold insert.
  rewrite (horizH1 n l i j a c H H1 H2 H3 H4 H5). 
  rewrite (horizH2 n l i j a c H H1 H2 H3 H4 H5). 
  rewrite (horizH3 n m i j b c H H0 H2 H3 H4 H6). 
  rewrite (horizH4 n m i j b c H H0 H2 H3 H4 H6). 
  repeat(rewrite  <- app_assoc).   
  reflexivity. 
Qed.

(*cast for horizontal associativity axiom in operadLaws*)
(*needed for type checking*)
Definition horizCast  {operad : Operad} (n m l i j : nat)(a b c : list T)(d:T)(p0: 2 <= n)(p1 : 1 <= m)(p2: 1 <= l)
  (q0: i < j)(q1: j < n)(r0: length c = n)(r1: length a = l)(r2 : length b = m)
  (e: El (operad〘d, insert (l-1 + j) (insert i c a) b〙)) : El (operad 〘d, insert i (insert j c b) a〙). 
Proof.
  rewrite (@horizInsert T n m l i j a b c p0 p1 p2 q0 q1 r0 r1 r2) in e. apply e. 
Defined. 

(*In order to finish our formal definition of colored operads, 
we need to define the laws that an operad must follow*)

(* Since operad compositions will be defined only under an assumption on the length of the list c,
and the operad laws include several cases where the list c is generated by inserting a new list into an 
old list, we need a lemma giving the length of such a list.*)
Lemma insertlength {A : Type} {i n m :nat} {old new : list A} (l_old : length old = n) (l_new : length new = m)
  (i_old : i < n) :
  length (insert i old new) = n + m - 1.
Proof.
unfold insert. rewrite app_length.
assert (H1 : length (firstn i old) = i). { rewrite firstn_length. rewrite l_old. sauto. } rewrite H1.
rewrite app_length. rewrite l_new. rewrite skipn_length. rewrite l_old. sauto.
Qed.



(* Operad compositions will also be defined only under the assumptions that 1 <= n and i < n. 
Thus, in order to state the compositions that appear in the operad law statements, we need to reference
such inequalities for various values of n and i. These lemmas provide the necessary references:*)
Lemma i_sum_ineq {i j m n : nat} (i0 : i < n) (i1 : j < m) : i + j < n + m - 1.
Proof.
sauto.
Qed.


Lemma n_sum_ineq {m n : nat} (p0 : 1 <= n) (p1 : 1 <= m) : 1 <= n + m - 1.
Proof.
sauto.
Qed.



Lemma n_gt_ineq {i j : nat} (p0 : i < j) : 1 <= j.
Proof.
sauto.
Qed.

Lemma n_ge2_ineq {n : nat} (q0 : 2 <= n) : 1 <= n.
Proof.
sauto.
Qed.

Lemma i_addl1_ineq {j n l : nat} (q2 : 1 <= l) (p1 : j < n) : l-1+j < n+l-1.
Proof.
sauto.
Qed.

Lemma i_trans_ineq {i j n m : nat} (p0 : i < j) (p1 : j < n) (q1 : 1 <= m) : i < n+m-1.
Proof.
sauto.
Qed.


(* These lemmas give some cases of lookup statements' interactions with inserted lists. 
These are also used in the statements of the operad laws. *)
Lemma vertLookup : forall {n m i j : nat} {bj : T}
          {b c : list T}
          (q1 : lookupT j b = bj)
          (r0: i < n)(r1: j < m) 
          (s0: length c = n)(s1: length b = m), lookupT (i+j) (insert i c b)   = bj.
Proof.
intros. unfold lookupT. unfold lookup. unfold insert.
assert (length (firstn i c) = i). { rewrite firstn_length. rewrite s0. sauto. }
assert (i + j - length (firstn i c) = j). sauto.
rewrite app_nth2. rewrite app_nth1. sauto. sauto. sauto.
Qed.

Lemma horizLookupL : forall {n i j : nat} {ci : T} {b c : list T} (p0: i < j) (p1 : j < n) (r0 : lookupT i c = ci) (s0: length c = n),
          lookupT i (insert j c b) = ci.
Proof.
intros. unfold lookupT. unfold lookup. unfold insert.
assert (length (firstn j c) = j). { rewrite firstn_length. rewrite s0. sauto. }
rewrite app_nth1. rewrite <- (app_nth1 _ (skipn j c)). rewrite firstn_skipn. assumption. sauto. sauto.
Qed.

Lemma horizLookupR : forall {n l i j : nat} {cj : T} {a c : list T} (p0 : i < j) (p1 : j < n) (q2 : 1 <= l) (r1 : lookupT j c = cj) (s0 : length c = n) (s2 : length a = l), 
          lookupT (l-1 + j) (insert i c a) = cj.
Proof.
intros. unfold lookupT. unfold lookup. unfold insert.
assert (length (firstn i c) = i). { rewrite firstn_length. rewrite s0. sauto. }
rewrite app_nth2; last first. sauto.
rewrite app_nth2; last first. sauto.
assert (length (firstn (i + 1) c) = i + 1). { rewrite firstn_length. sauto. }
assert (HH : l - 1 + j - length (firstn i c) - length a = j - length (firstn (i + 1) c)). sauto.
rewrite HH. rewrite <- (app_nth2 (firstn (i + 1) c)). rewrite firstn_skipn. assumption. sauto.
Qed.

Record operadLaws (operad : Operad) : Type :=
{
  opId: forall (d : T), El (operad 〘d, [d]〙)

; operadComp : forall (i n : nat) (d ci : T) (c b : list T) 
    (r : length c = n) (n1 : 1 <= n) (il : i < n), 
    lookupT i c= ci -> (El (operad 〘d,c〙)) * (El (operad 〘ci,b〙)) -> El (operad 〘d,insert i c b〙)

; unityL: forall (d : T) (c : list T) (e : El (operad〘d,c〙)),
   unityLCast(operadComp 0 1 d d [d] c eq_refl (le_n 1) PeanoNat.Nat.lt_0_1 eq_refl (opId d, e)) = e 

; unityR : forall (n i : nat) (d ci : T) (c : list T ) (p : lookupT i c = ci)(q0: 1 <= n)(q1: i < n) 
              (r: length c = n) (e : El (operad〘d,c〙)), 
            @unityRCast operad d ci c n i p q0 q1 r (operadComp i n d ci c (ci::nil) r q0 q1 p (e, opId ci)) = e

; vertAssoc: forall (n m l i j : nat) (d ci bj : T)
          (a b c : list T) 
          (p0: 1 <= n )(p1 : 1 <= m) (p2 : 1 <= l)
          (q0 : lookupT i c = ci) (q1 : lookupT j b = bj)
          (r0: i < n)(r1: j < m) 
          (s0: length c = n)(s1: length b = m)(s2: length a = l)
          (e : El (operad 〘d,c〙)) (f : El (operad 〘ci, b〙)) (g : El (operad 〘bj, a〙)), 
 @vertCast operad n m i j d a b c p0 p1 r0 r1 s0 s1 (operadComp (i+j) (n+m-1) d bj (insert i c b) a (insertlength s0 s1 r0) (n_sum_ineq p0 p1) (i_sum_ineq r0 r1) (vertLookup q1 r0 r1 s0 s1) (operadComp i n d ci c b s0 p0 r0  q0 (e, f), g)) = 
  operadComp i n d ci c (insert j b a) s0 p0 r0 q0 (e, operadComp  j m ci bj b a s1 p1 r1  q1 (f, g))

; horizAssoc: forall (n m l i j : nat) (d ci cj : T) 
          (a b c : list T ) 
          (p0 : i < j)(p1 : j < n)
          (q0: 2 <= n)(q1: 1 <= m)(q2: 1 <= l) 
          (r0 : lookupT i c = ci) (r1 : lookupT j c = cj)
          (s0: length c = n)(s1: length b = m)(s2: length a = l)
          (e : El (operad〘d,c〙)) (f : El (operad〘ci,a〙)) 
          (g : El (operad 〘cj,b〙)),
        @horizCast operad n m l i j a b c d q0 q1 q2 p0 p1 s0 s2 s1 (operadComp (l-1+j) (n+l-1) d cj (insert i c a) b (insertlength s0 s2 (PeanoNat.Nat.lt_trans i j n p0 p1))
                 (n_sum_ineq (n_ge2_ineq q0) q2) (i_addl1_ineq q2 p1) (horizLookupR p0 p1 q2 r1 s0 s2) (operadComp i n d ci c a s0 (n_ge2_ineq q0) (PeanoNat.Nat.lt_trans i j n p0 p1) r0 (e, f), g)) = 
        operadComp i (n+m-1) d ci (insert j c b) a (insertlength s0 s1 p1) (n_sum_ineq (n_ge2_ineq q0) q1) (i_trans_ineq p0 p1 q1) (horizLookupL p0 p1 r0 s0) (operadComp j n d cj c b s0 (n_ge2_ineq q0) p1 r1 (e, g), f)

; perm: forall (c c': list T)(d : T)
   (p: 1 <= length c ),
  Permutation c c' -> iso (El (operad〘d, c〙)) (El (operad〘d, c'〙))
}.


