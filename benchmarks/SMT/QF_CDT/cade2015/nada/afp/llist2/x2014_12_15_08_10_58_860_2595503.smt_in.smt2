;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort Nat_a_llist_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun i$ ()Nat$ )
(declare-fun t$ ()A_llist$ )
(declare-fun lrev$ (A_llist$ )A_llist$ )
(declare-fun plus$ (Nat$ Nat$ )Nat$ )
(declare-fun zero$ ()Nat$ )
(declare-fun ldrop$ (A_llist$ Nat$ )A_llist$ )
(declare-fun ltake$ (A_llist$ )Nat_a_llist_fun$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun fun_app$ (Nat_a_llist_fun$ Nat$ )A_llist$ )
(declare-fun inflsts$ (A_set$ )A_llist_set$ )
(declare-fun lappend$ (A_llist$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (Nat$ Nat$ )Bool )
(declare-fun llength$ (A_llist$ )Nat$ )
(declare-fun alllstsp$ (A_bool_fun$ A_llist$ )Bool )
(declare-fun finlstsp$ (A_bool_fun$ A_llist$ )Bool )
(declare-fun lbutlast$ (A_llist$ )A_llist$ )
(assert (! (not (= (llength$ (fun_app$ (ltake$ t$ )i$ ))i$ )):named a0 ))
(assert (! (not (= (ldrop$ t$ i$ )lNil$ )):named a1 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (ldrop$ lNil$ ?v0 )lNil$ ):pattern ((ldrop$ lNil$ ?v0 )))):named a2 ))
(assert (! (forall ((?v0 Nat$ ))(! (= (fun_app$ (ltake$ lNil$ )?v0 )lNil$ ):pattern ((fun_app$ (ltake$ lNil$ )?v0 )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(=> (not (= (ldrop$ ?v0 ?v1 )lNil$ ))(not (= ?v0 lNil$ )))):named a4 ))
(assert (! (= (lbutlast$ lNil$ )lNil$ ):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 Nat$ ))(=> (member$ ?v0 (inflsts$ ?v1 ))(= (llength$ (fun_app$ (ltake$ ?v0 )?v2 ))?v2 ))):named a6 ))
(assert (! (= (llength$ lNil$ )zero$ ):named a7 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ )(?v2 Nat$ ))(= (fun_app$ (ltake$ (ldrop$ ?v0 ?v1 ))?v2 )(ldrop$ (fun_app$ (ltake$ ?v0 )(plus$ ?v2 ?v1 ))?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (ltake$ ?v0 )zero$ )lNil$ ):pattern ((ltake$ ?v0 )))):named a9 ))
(assert (! (= (lrev$ lNil$ )lNil$ ):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 Nat$ ))(= (lappend$ (fun_app$ (ltake$ ?v0 )?v1 )(ldrop$ ?v0 ?v1 ))?v0 )):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(= (ldrop$ ?v2 ?v0 )lNil$ ))(= (ldrop$ ?v2 ?v1 )lNil$ ))):named a12 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(finlstsp$ ?v0 lNil$ )):named a13 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(alllstsp$ ?v0 lNil$ )):named a14 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (lappend$ ?v0 ?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= lNil$ (lappend$ ?v0 ?v1 ))(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a16 ))
(check-sat )
;(get-unsat-core )
