;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-datatypes ()((Nat_option$ (none$ )(some$ (the$ Nat$ )))(Enat$ (abs_enat$ (rep_enat$ Nat_option$ )))))
(declare-fun f$ ()A_a_fun$ )
(declare-fun x$ ()A$ )
(declare-fun lmap$ (A_a_fun$ A_llist$ )A_llist$ )
(declare-fun ldrop$ (Enat$ A_llist$ )A_llist$ )
(declare-fun lnull$ (A_llist$ )Bool )
(declare-fun ltake$ (Enat$ A_llist$ )A_llist$ )
(declare-fun ldropn$ (Nat$ A_llist$ )A_llist$ )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun lfinite$ (A_llist$ )Bool )
(declare-fun llength$ (A_llist$ )Enat$ )
(declare-fun iterates$ (A_a_fun$ A$ )A_llist$ )
(assert (! (not (= (lmap$ f$ (iterates$ f$ x$ ))(iterates$ f$ (fun_app$ f$ x$ )))):named a0 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_fun$ )(?v2 A_llist$ ))(= (ldrop$ ?v0 (lmap$ ?v1 ?v2 ))(lmap$ ?v1 (ldrop$ ?v0 ?v2 )))):named a1 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_a_fun$ )(?v2 A_llist$ ))(= (ldropn$ ?v0 (lmap$ ?v1 ?v2 ))(lmap$ ?v1 (ldropn$ ?v0 ?v2 )))):named a2 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (llength$ (lmap$ ?v0 ?v1 ))(llength$ ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lnull$ (iterates$ ?v0 ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(not (lfinite$ (iterates$ ?v0 ?v1 )))):named a5 ))
(assert (! (forall ((?v0 Enat$ )(?v1 A_a_fun$ )(?v2 A_llist$ ))(= (ltake$ ?v0 (lmap$ ?v1 ?v2 ))(lmap$ ?v1 (ltake$ ?v0 ?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (iterates$ ?v0 ?v1 )(lCons$ ?v1 (iterates$ ?v0 (fun_app$ ?v0 ?v1 ))))):named a7 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (lhd$ (iterates$ ?v0 ?v1 ))?v1 )):named a8 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (lnull$ (lmap$ ?v0 ?v1 ))(lnull$ ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (lfinite$ (lmap$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (ltl$ (iterates$ ?v0 ?v1 ))(iterates$ ?v0 (fun_app$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_llist$ ))(= (ltl$ (lmap$ ?v0 ?v1 ))(lmap$ ?v0 (ltl$ ?v1 )))):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(! (= (lfinite$ (lCons$ ?v0 ?v1 ))(lfinite$ ?v1 )):pattern ((lCons$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ ))(= (lfinite$ (ltl$ ?v0 ))(lfinite$ ?v0 ))):named a16 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_llist$ ))(= (lfinite$ (ldropn$ ?v0 ?v1 ))(lfinite$ ?v1 ))):named a17 ))
(check-sat )
;(get-unsat-core )
