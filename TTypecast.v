Require Import FunctionalExtensionality.
Require Import List.
From Coq Require Import Eqdep_dec.
From Operads Require Import Tarski.

(*Typecasting:*)
(*This is a general function for typecasts.*)
Definition typecast {A B : T} (eq : A=B) (e : El A) : El B.
Proof.
rewrite eq in e. apply e.
Defined.

(*We can compose casts:*)
Lemma typecastCompose {A B C : T} {eq1 : A=B} {eq2 : B=C} {e : El A} :
  typecast eq2 (typecast eq1 e) = typecast (eq_trans eq1 eq2) e.
Proof.
destruct eq1. destruct eq2. reflexivity.
Qed.

(*We define a typecast where the type is dependent on some other type A, i.e., 
  the type is a function of an argument of type A, and the two different formulations 
  of the type arise from two sides of an equation in A:*)
(* change to on lists?*)
(*Definition dep_typecast {a1 a2 : list T} {eq : a1=a2} {PA : list T -> T} (e : El (PA a1)): El (PA a2).*)
Definition dep_typecast {A : Type} {a1 a2 : A} {eq : a1=a2} {PA : A -> T} (e : El (PA a1)): El (PA a2).
Proof.
rewrite eq in e. apply e.
Defined.

(*Show that this is a typecast:*)
Lemma dep_typecast_is_typecast {A : Type} {a1 a2 : A} {eq : a1=a2} {PA : A -> T} :
  @dep_typecast A a1 a2 eq PA = typecast (f_equal PA eq).
Proof.
destruct eq. reflexivity.
Qed.

(*Typecast symmetry: if typecast x = y, then x = typecast y. 
  This is useful for moving a typecast to the other side.*)
Lemma typecastsym {A B : T} {eq : A=B} {x : El A} {y : El B} : 
  (typecast eq x = y) = (x = typecast (eq_sym eq) y).
Proof.
destruct eq. reflexivity.
Qed.

(*Self-typecast lemmas:
  The following few lemmas all express the idea that typecasts depend only on the types 
  involved, not on the particular equations used. For the most part these depend on the 
  eq_rect_eq axiom.*)

(*Typecasting with a reflexive equation is the identity.*)
Lemma typecastRefl {A : T} (x : El A) : x = typecast eq_refl x.
Proof.
reflexivity.
Qed.

(*Typecasting with an equation of reflexive type. Depends on eq_rect_eq axiom.*)
Lemma typecastSelf {A : T} {eq : A = A} (x : El A) : typecast eq x = x.
Proof.
unfold typecast. rewrite <- Eqdep_dec.eq_rect_eq_dec. reflexivity.
decide equality. decide equality.
Qed.

Lemma typecastAuto {A : T} {eq : A = A} : typecast eq = id.
Proof.
apply functional_extensionality. intros x. rewrite typecastSelf. reflexivity.
Qed.

(*Typecasts to the same type are equal:*)
Lemma typecastSame {A B : T} {eq1 eq2 : A = B} (x : El A) : typecast eq1 x = typecast eq2 x.
Proof.
(*rewrite typecastsym. rewrite typecastCompose. rewrite typecastSelf. reflexivity.*)
destruct eq1. symmetry. rewrite <- typecastRefl. apply typecastSelf.
Qed.

Lemma typecastType {A B : T} {eq1 eq2 : A = B} : typecast eq1 = typecast eq2.
Proof.
destruct eq1. rewrite typecastAuto. symmetry. apply typecastAuto.
Qed.

(*A lemma for rewriting typecasted function application:
  the typecast can be moved between the function and its output.
  This too depends on the eq_rect_eq axiom.*)
Lemma typecastFun {A B1 B2 : T} (eq : B1=B2) (eqF : fn A B1 = fn A B2) (f : El (fn A B1)) (x : El A) : 
  typecast eqF f x = typecast eq (f x).
Proof.
unfold typecast. destruct eq. rewrite <- Eqdep_dec.eq_rect_eq_dec. reflexivity.
decide equality. decide equality.
Qed.

(*Reverse typecasts cancel:*)
Lemma typecastK {A B : T} {eqAB : A=B} (x : El B) : typecast eqAB (typecast(eq_sym eqAB) x) = x.
Proof.
destruct eqAB. reflexivity.
Qed.

(*Using Coq's classes, we develop a notation for typecasting equations.*)

(*The class for typecasting equations:*)
Class Typeeq (a b : T) : Prop :=
  Type_eq : a = b.

(*The class for dependent-typecasting equations:*)
Class Depteq {A : Type} (a b : A) : Prop :=
  Dept_eq : a = b.

(*We can form a Typeeq from a Depteq:*)
#[global] Instance DepTypeeq {A : Type} {a b : A} {PA : A -> T} (de : Depteq a b) : 
  Typeeq (PA a) (PA b) := f_equal PA de.

(*Here we construct a tactic to rewrite a typecast from one equation to an equivalent one.*)
Lemma typecastTripleIntro {A B C D : T} (eq1 : A=B) (eq2 : C=D) (eq3 : A=C) (eq4 : D=B) :
  forall (e : El A), typecast(eq1) e = typecast(eq4) (typecast(eq2) (typecast(eq3) e)).
Proof.
intros e. rewrite !typecastCompose. apply typecastSame.
Qed.

Lemma typecastTripleOutro {C D : T} (eq2 : C=D) {eq3 : C=C} {eq4 : D=D} :
  forall (e : El C), typecast(eq4) (typecast(eq2) (typecast(eq3) e)) = typecast(eq2) e.
Proof.
intros e. rewrite !typecastAuto. reflexivity.
Qed.

(*If eq1 and eq2 both typecheck in Coq to Typeeqs of type A=B, then the following tactic rewrites a 
typecast from typecast eq1 to typecast eq2*)
Ltac retypecast eq1 eq2 := rewrite (typecastTripleIntro eq1 eq2 eq_refl eq_refl); 
                           rewrite (typecastTripleOutro eq2).

(*This tactic does the same with Depteqs*)
Ltac redepcast de1 de2 := rewrite (typecastTripleIntro (DepTypeeq(de1)) (DepTypeeq(de2)) eq_refl eq_refl);
                          rewrite (typecastTripleOutro (DepTypeeq(de2))).

(*The following lemmas are useful for moving equation manipulations into and out of a DepTypeeq.*)
Lemma DepTypeeq_sym {A : Type} {PA : A -> T} {a b : A} {de} : 
    eq_sym (DepTypeeq(PA:=PA) de) = @DepTypeeq A b a PA (eq_sym de).
Proof.
destruct de. reflexivity.
Qed.

Lemma DepTypeeq_trans {A : Type} {PA : A -> T} {a b c : A} {de1 : Depteq a b} {de2 : Depteq b c} :
    eq_trans (DepTypeeq(PA:=PA) de1) (DepTypeeq de2) = DepTypeeq (eq_trans de1 de2).
Proof.
destruct de1. destruct de2. reflexivity.
Qed.
 
(*This lemma transforms between typecasts dependent on type A and typecasts dependent on type B, 
  using a function from A to B. This may be useful to prepare applications of the latter 
  lemma, which requires that the two typecasts be dependent on the same type. *)
Lemma DepTypeeq_recast {A B : Type} (PB : B -> T) (AB : A -> B) {x y : A} {de : x = y} :
    DepTypeeq(PA:=fun a => PB (AB a)) de = DepTypeeq(PA:=PB) (f_equal AB de).
Proof.
destruct de. reflexivity.
Qed.

