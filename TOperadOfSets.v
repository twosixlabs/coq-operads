Require Import FunctionalExtensionality.
Require Import List.
From Hammer Require Import Hammer.
Require Import Permutation.

From Operads Require Import Typecast.
From Operads Require Import TColoredOperads.

(* This is a modfication of the definition of compose from the 
   multiCompose.v file to eliminate dependence on vectors,
   using lists instead. The type of the arguments is also changed from type to T, the 
   collection of types inductively defined in TColoredOperads.v.*)

Fixpoint arr (ts : list T) (t' : T) : T := match ts with
  | nil => t'
  | t :: ts => t → (arr ts t') end.

Lemma arr_equation_1 {t' : T} : arr nil t' = t'.
Proof.
reflexivity.
Qed.

Lemma arr_equation_2 {t t' : T} {ts : list T} : arr (t :: ts) t' = (t → arr ts t').
Proof.
reflexivity.
Qed.

Fixpoint compose' (bs : list T) {ci d : T} : El (ci → d) -> El (arr bs ci) -> El (arr bs d) := match bs with 
  | nil => fun f g => f g
  | b :: bs => fun f g x => compose' bs f (g x) end.

Lemma compose'_equation_1 {ci d : T} {f : El (ci → d)} {g : El ci} : compose' nil f g = f g.
Proof.
reflexivity.
Qed.

Lemma compose'_equation_2 {ci d b : T} {bs : list T} {f : El (ci → d)} {g : El (arr (b :: bs) ci)} : 
  compose' (b :: bs) f g = fun x => compose' bs f (g x).
Proof.
reflexivity.
Qed.

(* f : c0 -> ... -> cn-1 -> cn -> d   (* NB: d itself may be a function type *)
   g : b0 -> ... -> bm -> cn
   compose cs bs f g : c0 ... cn-1 b0 ... bm -> d
 *)
Fixpoint compose (cs : list T) {ci d : T} (bs : list T) 
  : El (arr cs (ci → d)) -> El (arr bs ci) -> El (arr cs (arr bs d)) := match cs with
  | nil => fun f g => compose' bs f g
  | c :: cs => fun f g x => compose cs bs (f x) g end.

Lemma compose_equation_1 {ci d : T} {bs : list T}:
  @compose nil ci d bs = compose' bs.
Proof.
reflexivity.
Qed.

Lemma compose_equation_2 {ci d c : T} {bs cs : list T} {f : El (arr (c :: cs) (ci → d))} {g : El (arr bs ci)} : 
  compose (c :: cs) bs f g = fun x => compose cs bs (f x) g.
Proof.
reflexivity.
Qed.

(* This is a useful equality of types. We give it a name to refer to it in typecasts. *)
Lemma arr_append {l1 l2 : list T} {d : T} : arr (l1 ++ l2) d = arr l1 (arr l2 d).
Proof.
induction l1 as [|h l1 IH].
- rewrite app_nil_l. reflexivity.
- rewrite <- app_comm_cons. rewrite arr_equation_2. rewrite IH. reflexivity.
Qed.

Lemma El_arr_append {l1 l2 : list T} {d : T} : El (arr (l1 ++ l2) d) = El (arr l1 (arr l2 d)).
Proof.
rewrite arr_append. reflexivity.
Qed.

(* And occasionally useful to apply it twice. We give this a name too. *)
Lemma double_arr_append {l1 l2 l3 : list T} {d : T} : 
  arr (l1 ++ l2 ++ l3) d = arr l1 (arr l2 (arr l3 d)).
Proof.
rewrite !arr_append. reflexivity.
Qed.

Lemma El_double_arr_append {l1 l2 l3 : list T} {d : T} : 
  El (arr (l1 ++ l2 ++ l3) d) = El (arr l1 (arr l2 (arr l3 d))).
Proof.
rewrite double_arr_append. reflexivity.
Qed.


(*We now define the multicomposition structure as an operad. *)

(*Note that the type associated with O (d , cs) is precisely arr cs d, so we construct a 
function that reverses the arguments of arr, and use that to construct the operad.*)

Definition arr_rev (t' : T) (ts : list T) : T := arr ts t'.

Definition setsOp : Operad := {| interp := arr_rev |}.

(*The units for our operad are identity functions: *)
Definition setsId (d : T) : El ( setsOp 〘 d, (d :: nil) 〙 ) := id.

(*The composition map is multicomposition as defined above.*)
(*Since the composition map is defined in terms of a product (A * B) -> C, 
and compose is defined as A -> B -> C, we need a way to translate one to the other.*)
Definition prod_map {A B C : Type} (f : A -> B -> C) (x : (A * B)) : C := f (fst x) (snd x).

(* We will also need to typecast various formulations involving the arr function. *)

(* This is the equality needed to typecast on the RHS of the composition definition: *)
Lemma insert_arr {i : nat} {d : T} {c b : list T} :
  arr (firstn i c) (arr b (arr (skipn (i + 1) c) d)) = arr (insert i c b) d.
Proof.
symmetry. apply double_arr_append.
Qed.

Lemma El_insert_arr {i : nat} {d : T} {c b : list T} :
  El (arr (firstn i c) (arr b (arr (skipn (i + 1) c) d))) = El (arr (insert i c b) d).
Proof.
rewrite insert_arr. reflexivity.
Qed.

(* And this is the equality needed to typecast on the LHS: *)
Lemma fn_arr {i n : nat} {d ci : T} {c : list T} (l : length c = n) (n1 : 1 <= n) 
  (il : i < n) (p : lookupT i c = ci) : 
  arr (firstn i c) (ci → (arr (skipn (i + 1) c) d)) = arr c d.
Proof.
rewrite <- arr_equation_2. rewrite <- arr_append. 
assert (ic: insert i c (ci :: nil) = c). apply (@unityRInsert T (|𝕦|) c ci n i n1 il l p). 
assert (ii: firstn i c ++ ci :: skipn (i + 1) c = insert i c (ci :: nil)). reflexivity.
rewrite ii. rewrite ic. reflexivity.
Qed.

Lemma El_fn_arr {i n : nat} {d ci : T} {c : list T} (l : length c = n) (n1 : 1 <= n) 
  (il : i < n) (p : lookupT i c = ci) : 
  El (arr (firstn i c) (ci → (arr (skipn (i + 1) c) d))) = El (arr c d).
Proof.
rewrite (fn_arr l n1 il p). reflexivity.
Qed.

(* The typecast for the RHS: *)
Definition insertCast {i : nat} {d : T} {c b : list T}
  (e : El (arr (firstn i c) (arr b (arr (skipn (i + 1) c) d)))) : 
   El (setsOp 〘d,insert i c b〙).
Proof.
rewrite El_insert_arr in e. apply e.
Defined.

(* The typecast for one component of the LHS: *)
Definition insertCast0 {i n : nat} {d ci : T} {c b : list T} 
  {l : length c = n} {n1 : 1 <= n} {il : i < n} (p : lookupT i c = ci)
  (e : El (setsOp 〘 d, c 〙) ) : 
  (El (arr (firstn i c) (ci → arr (skipn (i + 1) c) d)) ).
Proof.
rewrite (El_fn_arr l n1 il p). apply e.
Defined.

(*The typecast for the full LHS:*)
Definition insertCast1 {i n : nat} {d ci : T} {c b : list T} 
  {l : length c = n} {n1 : 1 <= n} {il : i < n} (p : lookupT i c = ci)
  (e :  El (setsOp 〘 d, c 〙) *  El (setsOp 〘 ci, b 〙)) : 
   El (arr (firstn i c) (ci → arr (skipn (i + 1) c) d)) * El (arr b ci) :=
(@insertCast0 i n d ci c b l n1 il p (fst e), snd e).

(* We are now ready to define the operad composition: *)
Definition setsComp (i : nat) {n : nat} {d ci : T} {c : list T} {b : list T} 
  {l : length c = n} {n1 : 1 <= n} {il : i < n} {p : lookupT i c = ci} : 
  ( El (setsOp 〘d,c〙) *  El (setsOp 〘ci,b〙) -> 
           El (setsOp 〘d,insert i c b〙)) :=    fun x => 
            insertCast ((prod_map (@compose (firstn i c) ci (arr (skipn (i + 1) c) d) b))
                (@insertCast1 i n d ci c b l n1 il p x)). 

(* Composing with an identity function returns the same function:*)
Lemma compose'_id {d : T} {b : list T} {g : El (arr b d)} : compose' b (setsId d) g = g.
Proof.
induction b as [|h b IH].
- reflexivity. 
- rewrite compose'_equation_2.
  apply functional_extensionality. intros x. apply IH.
Qed.

(*The following lemmas show that the typecasts used in the operad definition are dep_typecasts, 
and therefore typecasts:*)
Lemma unityLCast_is_dept {operad : Operad} {d : T} {c : list T} :
  @unityLCast operad d c = dep_typecast 
        (PA := fun x => El ( operad〘d,x〙))(eq:=(unityLInsert c)).
Proof.
reflexivity.
Qed.

Lemma unityLCast_is_typecast {operad : Operad}{d : T} {c : list T} :
  @unityLCast operad d c = typecast (DepTypeeq (PA:=(fun x => El ( operad〘d,x〙))) (unityLInsert c)).
Proof.
rewrite unityLCast_is_dept. rewrite dep_typecast_is_typecast. reflexivity.
Qed.


Lemma unityRCast_is_dept {operad : Operad}{d ci:T}{c: list T}(n i: nat)(p: lookupT i c = ci)(q0: 1 <= n)
  (q1: i < n)(r: length c = n) :
  @unityRCast operad d ci c n i p q0 q1 r = dep_typecast (PA := fun x => El (operad〘d,x〙)) 
    (eq:= (@unityRInsert T (|𝕦|) c ci n i q0 q1 r p)).
Proof.
reflexivity.
Qed. 

Lemma unityRCast_is_typecast {operad : Operad}{d ci:T}{c: list T}(n i: nat)(p: lookupT i c = ci)(q0: 1 <= n)
  (q1: i < n)(r: length c = n) :
  @unityRCast operad d ci c n i p q0 q1 r = typecast (DepTypeeq (PA:= fun x => El (operad〘d,x〙))
    (@unityRInsert T (|𝕦|) c ci n i q0 q1 r p)).
Proof.
rewrite unityRCast_is_dept. rewrite dep_typecast_is_typecast. reflexivity.
Qed.

Lemma vertCast_is_dept{operad : Operad} {n m i j : nat}
          {d: T} {a b c : list T} {p0: 1 <= n}{p1 : 1 <= m}{p2: i < n} 
            {p3: j < m} {p4: length c = n}{p5: length b = m} :
  @vertCast operad n m i j d a b c p0 p1 p2 p3 p4 p5  = dep_typecast (PA := fun x => El (operad〘d,x〙)) 
    (eq:= (vertInsert n m i j a b c p0 p1 p2 p3 p4 p5) ).
Proof.
reflexivity.
Qed.

Lemma vertCast_is_typecast{operad : Operad} {n m i j : nat}
          {d: T} {a b c : list T} {p0: 1 <= n}{p1 : 1 <= m}{p2: i < n} 
            {p3: j < m} {p4: length c = n}{p5: length b = m} :
  @vertCast operad n m i j d a b c p0 p1 p2 p3 p4 p5  = typecast (DepTypeeq (PA:= fun x => El (operad〘d,x〙))
    (vertInsert n m i j a b c p0 p1 p2 p3 p4 p5)).
Proof.
rewrite vertCast_is_dept. rewrite dep_typecast_is_typecast. reflexivity.
Qed.

Lemma horizCast_is_dept{operad : Operad} {n m l i j : nat} {d : T}
          {a b c : list T} {q0 : 2 <= n} {q1 : 1<=m} {q2 : 1<=l} {p0: i<j} {p1: j<n}
          {s0 : length c = n} {s1 : length b = m} {s2 : length a = l} :
  @horizCast operad n m l i j a b c d q0 q1 q2 p0 p1 s0 s2 s1 = dep_typecast (PA:= fun x => El (operad〘d,x〙))
    (eq:= @horizInsert T n m l i j a b c q0 q1 q2 p0 p1 s0 s2 s1).
Proof.
reflexivity.
Qed.

Lemma horizCast_is_typecast{operad : Operad} {n m l i j : nat} {d : T}
          {a b c : list T} {q0 : 2 <= n} {q1 : 1<=m} {q2 : 1<=l} {p0: i<j} {p1: j<n}
          {s0 : length c = n} {s1 : length b = m} {s2 : length a = l} :
  @horizCast operad n m l i j a b c d q0 q1 q2 p0 p1 s0 s2 s1 = typecast (DepTypeeq  (PA:= fun x => El (operad〘d,x〙))
    (@horizInsert T n m l i j a b c q0 q1 q2 p0 p1 s0 s2 s1)).
Proof.
rewrite horizCast_is_dept. rewrite dep_typecast_is_typecast. reflexivity.
Qed.

Lemma insertCast_is_typecast {i : nat} {d : T} {c b : list T} :
  @insertCast i d c b = typecast El_insert_arr.
Proof.
reflexivity.
Qed.

Lemma insertCast0_is_typecast {i n : nat} {d ci : T} {c b : list T} 
  {l : length c = n} {n1 : 1 <= n} {il : i < n} {p : lookupT i c = ci} :
  @insertCast0 i n d ci c b l n1 il p = typecast 
  (eq_sym(El_fn_arr l n1 il p)).
Proof.
reflexivity.
Qed.

(*We now lead up to showing that the left unity axiom is satisfied: *)
Lemma insertCast0_nil_is_id {d : T} {b : list T}: 
    @insertCast0 0 1 d d (d :: nil) b eq_refl (le_n 1) PeanoNat.Nat.lt_0_1 eq_refl = id.
Proof.
rewrite insertCast0_is_typecast. apply typecastAuto.
Qed.

(*Composition in our operad, with the operad identity in the first argument, is the identity:*)
Lemma setsComp_id {d : T} (b : list T) {e : El (arr b d)} {eq : insert 0 (d :: nil) b = b} : 
    unityLCast( @setsComp 0 1 d d (d :: nil) b eq_refl (le_n 1) PeanoNat.Nat.lt_0_1 eq_refl 
                (setsId d, e) ) = e.
Proof.
unfold setsComp. unfold prod_map. simpl.
rewrite insertCast0_nil_is_id. rewrite compose'_id. 
rewrite unityLCast_is_typecast. rewrite insertCast_is_typecast. rewrite typecastCompose.
apply typecastSelf.
Qed.

(*The left unity axiom is satisfied:*)
Lemma sets_unityL (d : T) (b : list T) (e : El ( setsOp 〘 d, b 〙 ) ) : 
  unityLCast(@setsComp 0 1 d d (d :: nil) b eq_refl (le_n 1) PeanoNat.Nat.lt_0_1 eq_refl (setsId d, e)) = e.
Proof.
apply setsComp_id. apply unityLInsert.
Qed.

(* Composing with an identity function in the second argument returns the same function: *)
Lemma compose_id {cs : list T} {ci d : T} (f : El (arr cs (ci → d))): 
    compose (d:=d) cs (ci::nil) f id = f.
Proof.
induction cs as [|h cs IH].
- rewrite compose_equation_1. apply (compose'_equation_2 (bs:=nil)).
- rewrite compose_equation_2. apply functional_extensionality. intros x. apply IH.
Qed.

(* The right unity axiom is satisfied: *)
Lemma sets_unityR (n i : nat) (d ci : T) (c : list T ) (p : lookupT i c = ci)(q0: 1 <= n)(q1: i < n) 
              (r: length c = n) (e : El (setsOp〘d,c〙)) : 
  @unityRCast setsOp d ci c n i p q0 q1 r (@setsComp i n d ci c (ci::nil) r q0 q1 p (e, setsId ci)) = e.
Proof.
unfold setsComp. unfold prod_map. simpl. rewrite compose_id.
rewrite unityRCast_is_typecast. rewrite insertCast_is_typecast. rewrite insertCast0_is_typecast.
rewrite typecastCompose. rewrite typecastCompose.
apply typecastSelf.
Qed.

(*For the associativity axioms, we prove a series of lemmas about associativity of the compose functions.*)
(*First, compose' is associative with no intermediate types:*)
Lemma compose'assoc' {d ci bj : T} {a : list T}
  (f : El (bj → ci)) (g : El (arr a bj)) (e : El (ci → d)) :
  compose' a e (compose' a f g) = compose' a (compose' (bj::nil) e f) g.
Proof.
induction a as [|h a IH].
- reflexivity.
- rewrite !compose'_equation_2. apply functional_extensionality. intros x. apply IH.
Qed.

(* compose' is associative with an intermediate type list: *)
Lemma compose'assoc {d ci bj : T} {a b1 : list T}
  (f : El (bj → (arr b1 ci))) (g : El (arr a bj)) (e : El (ci → d)) :
  compose' (a++b1) e (typecast (eq_sym El_arr_append) (compose' a f g)) = 
    typecast (eq_sym El_arr_append) (compose' a (compose' (bj::b1) e f) g).
Proof.
induction a as [|h a IH].
- simpl. rewrite !typecastSelf. reflexivity.
- simpl. apply functional_extensionality.  intros x.
  rewrite !(typecastFun (eq_sym El_arr_append)).
  apply IH.
Qed.

Lemma compose_assoc {c0 c1 b0 b1 a cb b :list T} {d ci bj abcd : T}
  (eqcb: cb = c0 ++ b0)
  (eqb : b = b0 ++ bj::b1)
  (eqabcd : abcd = arr b1 (arr c1 d))
  {eqf : Typeeq (El (arr b ci)) (El (arr b0 (bj → arr b1 ci)))}
  {eqcef:Typeeq (El (arr c0 (arr b (arr c1 d)))) (El (arr (cb) (bj → abcd)))}
  {eqcfg:Typeeq (El (arr b0 (arr a (arr b1 ci)))) (El (arr (b0++a++b1) ci))}
  {eqt : Typeeq (El (arr c0 (arr (b0++a++b1) (arr c1 d)))) (El (arr (cb) (arr a abcd)))}
   (e : El (arr c0 (ci → (arr c1 d)))) (f : El (arr b ci)) (g : El (arr a bj)):
  compose cb a (typecast eqcef (compose c0 b e f)) g = 
      typecast eqt (compose c0 (b0++a++b1) e (typecast eqcfg (compose b0 a (typecast eqf f) g))).
Proof.
revert eqf eqcef eqcfg eqt f. rewrite eqcb. rewrite eqabcd. rewrite eqb.
intros eqf eqcef eqcfg eqt f. clear eqcb eqabcd eqb cb abcd b.
induction c0 as [|hc0 c0 IHc0].
- simpl. induction b0 as [|hb0 b0 IHb0].
  + simpl. rewrite !typecastSelf.
    retypecast eqcfg (eq_sym (@El_arr_append a b1 ci)). rewrite compose'assoc.
    rewrite typecastCompose. symmetry. apply typecastSelf.
  + simpl. apply functional_extensionality. intros x.
    rewrite (typecastFun (@El_arr_append b0 (bj::b1) (arr c1 d))).
    rewrite (typecastFun El_double_arr_append).
    rewrite (typecastFun (eq_sym El_double_arr_append)).
    rewrite (typecastFun (@El_arr_append b0 (bj::b1) ci)).
    apply IHb0.
- simpl. apply functional_extensionality. intros x.
  assert (eqcefI : Typeeq (El (arr c0 (arr (b0 ++ bj :: b1) (arr c1 d))))
                    (El (arr (c0 ++ b0) (bj → arr b1 (arr c1 d))))).
    rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqcefI).
  assert (eqtI : Typeeq (El (arr c0 (arr (b0 ++ a ++ b1) (arr c1 d))))
                  (El (arr (c0 ++ b0) (arr a (arr b1 (arr c1 d)))))).
    rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqtI).
  apply IHc0.
Qed.

(* Vertical associativity axiom is satisfied: *)
Lemma sets_vertAssoc (n m l i j : nat) (d ci bj : T)
          (a b c : list T) 
          (p0: 1 <= n )(p1 : 1 <= m) (p2 : 1 <= l)
          (q0 : lookupT i c = ci) (q1 : lookupT j b = bj)
          (r0: i < n)(r1: j < m) 
          (s0: length c = n)(s1: length b = m)(s2: length a = l)
          (e : El (setsOp 〘d,c〙)) (f : El (setsOp 〘ci, b〙)) (g : El (setsOp 〘bj, a〙)): 
 @vertCast setsOp n m i j d a b c p0 p1 r0 r1 s0 s1 
        (@setsComp (i+j) (n+m-1) d bj (insert i c b) a (insertlength s0 s1 r0) (n_sum_ineq p0 p1) (i_sum_ineq r0 r1) (vertLookup q1 r0 r1 s0 s1) 
              (@setsComp i n d ci c b s0 p0 r0 q0 (e, f), g)) = 
  @setsComp i n d ci c (insert j b a) s0 p0 r0 q0 (e, @setsComp j m ci bj b a s1 p1 r1 q1 (f, g)).
Proof.
unfold setsComp. unfold prod_map. simpl.
rewrite vertCast_is_typecast. rewrite !insertCast_is_typecast. rewrite !insertCast0_is_typecast.
rewrite typecastsym. rewrite typecastsym. rewrite typecastCompose. rewrite typecastCompose. rewrite typecastCompose.
apply compose_assoc.
- apply (vertH1 n m). assumption. assumption. assumption. assumption.
- assert (B' : bj::(skipn (j+1) b) = skipn j b). {
    clear q0 r0 s0 s2 e f g.
    generalize dependent b. generalize dependent m. induction j.
    - sauto.
    - intros m p1 r1 b q1 s1.
      destruct b as [| b0 b].
      + sauto.
      + rewrite skipn_cons. rewrite plus_Sn_m. rewrite skipn_cons.
        apply (IHj (pred m)). sauto. sauto. sauto. sauto. }
  rewrite B'. symmetry. apply firstn_skipn.
- rewrite <- arr_append. f_equal. 
  apply (vertH2 n m). assumption. assumption. assumption. assumption.
Qed.

(* Compose associativity lemma for the horizontal direction, with equivalences built in:*)
Lemma compose_horizAssoc {a b c c0 c0' c1 c2 c2' c0a1 c0i1 c1b2 c1j2 : list T} {d ci cj : T}
     (c0eq : c0' = c0)
     (c2eq : c2' = c2)
     (eqa : c0a1 = c0 ++ a ++ c1)
     (eqi : c0i1 = c0 ++ ci::c1)
     (eqb : c1b2 = c1 ++ b ++ c2)
     (eqj : c1j2 = c1 ++ cj::c2)
     (eqc : c = c0 ++ (ci::c1) ++ (cj::c2))
     {eqc0 : El (arr c d) = El (arr c0 (ci → (arr c1j2 d)))}
     {eqc1 : El (arr c d) = El (arr c0i1 (cj → (arr c2 d)))}
     {eqcef : El (arr c0 (arr a (arr c1j2 d))) = El (arr c0a1 (cj → (arr c2' d)))}
     {eqceg : El (arr c0i1 (arr b (arr c2 d))) = El (arr c0' (ci → (arr c1b2 d)))}
     {eqt : El (arr c0' (arr a (arr c1b2 d))) = El (arr c0a1 (arr b (arr c2' d)))}
     (e : El (setsOp〘d,c〙))
     (f : El (setsOp〘ci,a〙))
     (g : El (setsOp 〘cj,b〙)) :
  compose c0a1 b (typecast eqcef (compose c0 a (typecast eqc0 e) f)) g
  = typecast eqt (compose c0' a 
          (typecast eqceg (compose c0i1 b (typecast eqc1 e) g)) f).
Proof.
revert eqc0 eqc1 eqcef eqceg eqt e. rewrite c0eq. rewrite c2eq. rewrite eqa. rewrite eqi. rewrite eqb. rewrite eqj. rewrite eqc. 
intros eqc0 eqc1 eqcef eqceg eqt e. clear c0eq c2eq eqa eqi eqb eqj eqc c0a1 c0i1 c1b2 c1j2 c.
induction c0 as [|hc0 tc0 IHc0].
- simpl in eqc0. simpl in eqc1.
  induction a as [|ha0 a0 IHa0].
  + simpl in eqcef. simpl in eqt. simpl in eqceg. 
    simpl.
    rewrite (typecastFun (eq_sym El_double_arr_append)).
    rewrite typecastCompose. rewrite !typecastSelf.
    f_equal. symmetry. apply typecastFun.
  + simpl in IHa0. simpl.
    apply functional_extensionality. intros x.
    assert (eqcefI : El (arr a0 (arr (c1 ++ cj :: c2) d)) =
                  El (arr (a0 ++ c1) (cj → arr c2 d))).
      rewrite !arr_append. reflexivity.
    rewrite (typecastFun eqcefI).
    assert (eqtI : El (arr a0 (arr (c1 ++ b ++ c2) d)) =
                El (arr (a0 ++ c1) (arr b (arr c2 d)))).
      rewrite !arr_append. reflexivity.
    rewrite (typecastFun eqtI).
    apply IHa0.
- apply functional_extensionality. intros x. simpl.
  assert (eqcefI : El (arr tc0 (arr a (arr (c1 ++ cj :: c2) d))) =
                  El (arr (tc0 ++ a ++ c1) (cj → arr c2 d))).
      rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqcefI).
  assert (eqtI : El (arr tc0 (arr a (arr (c1 ++ b ++ c2) d))) =
                El (arr (tc0 ++ a ++ c1) (arr b (arr c2 d)))).
      rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqtI).
  assert (eqcegI : El (arr (tc0 ++ ci :: c1) (arr b (arr c2 d))) =
                  El (arr tc0 (ci → arr (c1 ++ b ++ c2) d))).
      rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqcegI).
  assert (eqc0I : El (arr (tc0 ++ (ci :: c1) ++ cj :: c2) d) =
                 El (arr tc0 (ci → arr (c1 ++ cj :: c2) d))).
      rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqc0I).
  assert (eqc1I : El (arr (tc0 ++ (ci :: c1) ++ cj :: c2) d) =
                 El (arr (tc0 ++ ci :: c1) (cj → arr c2 d))).
      rewrite !arr_append. reflexivity.
  rewrite (typecastFun eqc1I).
  apply IHc0.
Qed.

(* Horizontal associativity axiom is satisfied:*)
Lemma sets_horizAssoc : forall (n m l i j : nat) (d ci cj : T) 
          (a b c : list T ) 
          (p0 : i < j)(p1 : j < n)
          (q0: 2 <= n)(q1: 1 <= m)(q2: 1 <= l) 
          (r0 : lookupT i c = ci) (r1 : lookupT j c = cj)
          (s0: length c = n)(s1: length b = m)(s2: length a = l)
          (e : El (setsOp〘d,c〙)) (f : El (setsOp〘ci,a〙))
          (g : El (setsOp 〘cj,b〙)),
        @horizCast setsOp n m l i j a b c d q0 q1 q2 p0 p1 s0 s2 s1 
        (@setsComp (l-1+j) (n+l-1) d cj (insert i c a) b (insertlength s0 s2 (PeanoNat.Nat.lt_trans i j n p0 p1))
                 (n_sum_ineq (n_ge2_ineq q0) q2) (i_addl1_ineq q2 p1) (horizLookupR p0 p1 q2 r1 s0 s2)
        (@setsComp i n d ci c a s0 (n_ge2_ineq q0) (PeanoNat.Nat.lt_trans i j n p0 p1) r0 (e, f), g)) = 
        @setsComp i (n+m-1) d ci (insert j c b) a (insertlength s0 s1 p1) (n_sum_ineq (n_ge2_ineq q0) q1) (i_trans_ineq p0 p1 q1) (horizLookupL p0 p1 r0 s0) 
        (@setsComp j n d cj c b s0 (n_ge2_ineq q0) p1 r1 (e, g), f).
Proof.
intros n m l i j d ci cj a b c p0 p1 q0 q1 q2 r0 r1 s0 s1 s2 e f g.
rewrite !horizCast_is_typecast.
unfold setsComp. unfold prod_map. simpl.
rewrite !insertCast_is_typecast. rewrite !insertCast0_is_typecast.
rewrite !typecastsym. rewrite !typecastCompose.
assert (HJ : forall L, skipn (i+1) (firstn j c) ++ L = skipn (i+1) (firstn j c ++ L)).
      intros L. rewrite skipn_app. f_equal. rewrite firstn_length. rewrite s0.
      assert (H : i + 1 - min j n = 0). sauto. rewrite H. apply skipn_O.
apply (compose_horizAssoc(c1:=skipn (i + 1) (firstn j c))).
- apply (horizH3 n m i j b c q0 q1 p0 p1 s0 s1).
- apply (horizH2 n l i j a c q0 q2 p0 p1 s0 s2).
- apply (horizH1 n l i j a c q0 q2 p0 p1 s0 s2).
- assert (H : firstn i c = firstn i (firstn j c)).
      rewrite firstn_firstn. f_equal. sauto.
  rewrite H. clear H HJ.
  assert (s4 : length (firstn j c) = j). rewrite firstn_length. sauto.
  assert (r4 : lookupT i (firstn j c) = ci). {
      clear r1 s1 s2 e f g.
      generalize dependent c.  generalize dependent ci. generalize dependent j. 
      generalize dependent n. induction i as [|i IHi].
      + intros n q0 j p0 p1 ci c r0 s0 s4. rewrite <- r0. destruct j.
        * sauto.
        * sauto.
      + intros n q0 j p0 p1 ci c r0 s0 s4. destruct c as [|h c].
        * sauto.
        * assert (H : firstn j (h :: c) = h :: firstn (pred j) c).
              assert (H' : j = S (pred j)). sauto. rewrite H'. sauto. rewrite H.
          apply (IHi (pred n)). sauto. sauto. sauto. sauto. sauto.
          rewrite firstn_length. sauto. } 
  symmetry. apply (@unityRInsert T (|𝕦|) (firstn j c) ci j i (n_gt_ineq p0) p0 s4 r4).
- apply (horizH4 n m i j b c q0 q1 p0 p1 s0 s1).
- rewrite HJ. f_equal. symmetry. apply (@unityRInsert T (|𝕦|) c cj n j (n_ge2_ineq q0) p1 s0 r1).
- rewrite <- app_comm_cons. rewrite HJ.
  assert (H: firstn j c ++ cj:: skipn (j+1) c = c).
      apply (@unityRInsert T (|𝕦|) c cj n j (n_ge2_ineq q0) p1 s0 r1).
  rewrite H. symmetry.
  apply (@unityRInsert T (|𝕦|) c ci n i (n_ge2_ineq q0) (PeanoNat.Nat.lt_trans i j n p0 p1) s0 r0).
Qed.

(*Some lemmas about isomorphism and function composition:*)
Lemma isoSelf {X : Type} : iso X X.
Proof.
exists id. exists id. split. reflexivity. reflexivity.
Qed.

Lemma isoFun {X Y Z : Type} : iso X Y -> iso (Z -> X) (Z -> Y).
Proof.
intros H. destruct H as [f H]. destruct H as [g H].
exists (fun F => (fun z => f (F z))).
exists (fun G => (fun z => g (G z))).
destruct H as [Hfg Hgf].
split.
- unfold comp. unfold comp in Hfg.
  apply functional_extensionality. intros G.
  apply functional_extensionality. intros z.
  apply (equal_f Hfg).
- unfold comp. unfold comp in Hgf.
  apply functional_extensionality. intros F.
  apply functional_extensionality. intros z.
  apply (equal_f Hgf).
Qed.

Lemma compassoc {A B C D} (f : A->B) (g: B->C) (h: C->D) : comp h (comp g f) = comp (comp h g) f.
Proof.
reflexivity.
Qed.

Lemma comp_f_id {A B} (f : A->B) : comp f id = f.
Proof.
reflexivity.
Qed.

Lemma isoTrans {X Y Z : Type} : iso X Y -> iso Y Z -> iso X Z.
Proof.
intros iXY iYZ.
destruct iXY as [fXY iXY]. destruct iYZ as [fYZ iYZ].
destruct iXY as [gXY iXY]. destruct iYZ as [gYZ iYZ].
destruct iXY as [fgXY gfXY]. destruct iYZ as [fgYZ gfYZ].
exists (comp fYZ fXY). exists (comp gXY gYZ). split.
- rewrite compassoc. rewrite <- (compassoc gXY fXY fYZ). rewrite fgXY.
  rewrite comp_f_id. apply fgYZ.
- rewrite compassoc. rewrite <- (compassoc fYZ gYZ gXY). rewrite gfYZ.
  rewrite comp_f_id. apply gfXY.
Qed.

(*Permutation axiom is satisfied:*)
Lemma setsPerm : forall (c c': list T)(d : T)
   (p: 1 <= length c ),
  Permutation c c' -> iso (El (setsOp〘d, c〙)) (El (setsOp〘d, c'〙)).
Proof.
intros c c' d l p.
induction p as [| h c c' | h h' c | c c' c'' p1 IHp1].
- apply isoSelf.
- destruct c.
  + rewrite (Permutation_nil p). apply isoSelf.
  + assert (L : 1 <= length (h::c)). sauto. apply (isoFun (IHp L)).
- exists (fun F => (fun X => (fun Y => F Y X))).
  exists (fun G => (fun Y => (fun X => G X Y))).
  split. reflexivity. reflexivity.
- assert (l' : 1 <= length c'). rewrite (Permutation_length p1) in l. apply l.
  apply (isoTrans (IHp1 l) (IHp2 l')).
Qed.

(*Final statement showing that all operad laws are satisfied:*)
Definition setsLaws : operadLaws setsOp := {|
  opId := setsId;
  operadComp := setsComp;
  unityL := sets_unityL;
  unityR := sets_unityR;
  vertAssoc := sets_vertAssoc;
  horizAssoc := sets_horizAssoc;
  perm := setsPerm |}.

