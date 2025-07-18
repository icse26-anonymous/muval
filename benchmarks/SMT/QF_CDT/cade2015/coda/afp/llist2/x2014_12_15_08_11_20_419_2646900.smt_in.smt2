;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-codatatypes ()((A_llist$ (lNil$ )(lCons$ (lhd$ A$ )(ltl$ A_llist$ )))))
(declare-fun l$ ()A_llist$ )
(declare-fun x$ ()A$ )
(declare-fun llast$ (A_llist$ )A$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun fpslsts$ (A_set$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun lbutlast$ (A_llist$ )A_llist$ )
(assert (! (not (= (lbutlast$ (fun_app$ (lappend$ l$ )(lCons$ x$ lNil$ )))l$ )):named a0 ))
(assert (! (= l$ lNil$ ):named a1 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= lNil$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (fun_app$ (lappend$ ?v0 )?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a3 ))
(assert (! (= (lbutlast$ lNil$ )lNil$ ):named a4 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (=> (= ?v0 lNil$ )false )(forall ((?v1 A$ )(?v2 A_llist$ ))(=> (= ?v0 (lCons$ ?v1 ?v2 ))false )))false )):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= lNil$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (fun_app$ (lappend$ ?v0 )?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a7 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ lNil$ )?v0 )?v0 ):pattern ((fun_app$ (lappend$ lNil$ )?v0 )))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A_llist$ ))(! (= (fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )(lCons$ ?v0 (fun_app$ (lappend$ ?v1 )?v2 ))):pattern ((fun_app$ (lappend$ (lCons$ ?v0 ?v1 ))?v2 )))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A$ )(?v2 A_llist$ ))(= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0 )(lCons$ ?v1 lNil$ )))?v2 )(fun_app$ (lappend$ ?v0 )(lCons$ ?v1 ?v2 )))):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ )(?v2 A$ )(?v3 A_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a12 ))
(assert (! (= (fun_app$ (lappend$ lNil$ )lNil$ )lNil$ ):named a13 ))
(assert (! (forall ((?v0 A_llist$ ))(= (not (= ?v0 lNil$ ))(exists ((?v1 A$ )(?v2 A_llist$ ))(= ?v0 (lCons$ ?v1 ?v2 ))))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A_llist$ ))(not (= lNil$ (lCons$ ?v0 ?v1 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (member$ ?v0 (fpslsts$ ?v1 ))(= ?v0 (fun_app$ (lappend$ (lbutlast$ ?v0 ))(lCons$ (llast$ ?v0 )lNil$ ))))):named a16 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A$ ))(=> (member$ ?v0 (finlsts$ ?v1 ))(= (lbutlast$ (lCons$ ?v2 ?v0 ))(ite (= ?v0 lNil$ )lNil$ (lCons$ ?v2 (lbutlast$ ?v0 )))))):named a17 ))
(check-sat )
;(get-unsat-core )
