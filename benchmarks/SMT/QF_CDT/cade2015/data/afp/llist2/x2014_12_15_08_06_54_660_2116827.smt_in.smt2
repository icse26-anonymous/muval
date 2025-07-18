;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_a_set_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun s$ ()A_llist$ )
(declare-fun t$ ()A_llist$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun alllsts$ (A_set$ )A_llist_set$ )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun inflsts$ (A_set$ )A_llist_set$ )
(declare-fun lappend$ (A_llist$ )A_llist_a_llist_fun$ )
(declare-fun lmember$ (A$ )A_llist_bool_fun$ )
(declare-fun poslsts$ (A_set$ )A_llist_set$ )
(declare-fun alllstsp$ (A_bool_fun$ A_llist$ )Bool )
(declare-fun finlstsp$ (A_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$a (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun fun_app$b (A_llist_a_set_fun$ A_llist$ )A_set$ )
(declare-fun gen_lset$ (A_set$ )A_llist_a_set_fun$ )
(assert (! (not (= (= lNil$ (fun_app$ (lappend$ s$ )t$ ))(and (= s$ lNil$ )(= t$ lNil$ )))):named a0 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ ?v0 )lNil$ )?v0 ):pattern ((lappend$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_llist$ ))(! (= (fun_app$ (lappend$ lNil$ )?v0 )?v0 ):pattern ((fun_app$ (lappend$ lNil$ )?v0 )))):named a2 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= lNil$ (fun_app$ (lappend$ ?v0 )?v1 ))(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= (fun_app$ (lappend$ ?v0 )?v1 )lNil$ )(and (= ?v0 lNil$ )(= ?v1 lNil$ )))):named a4 ))
(assert (! (= (fun_app$ (lappend$ lNil$ )lNil$ )lNil$ ):named a5 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(= (fun_app$ (lappend$ (fun_app$ (lappend$ ?v0 )?v1 ))?v2 )(fun_app$ (lappend$ ?v0 )(fun_app$ (lappend$ ?v1 )?v2 )))):named a6 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_llist$ ))(=> (member$ ?v0 (inflsts$ ?v1 ))(= (fun_app$ (lappend$ ?v0 )?v2 )?v0 ))):named a7 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(finlstsp$ ?v0 lNil$ )):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(alllstsp$ ?v0 lNil$ )):named a9 ))
(assert (! (forall ((?v0 A_set$ ))(member$ lNil$ (alllsts$ ?v0 ))):named a10 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (member$ ?v0 (inflsts$ ?v1 ))(member$ ?v0 (alllsts$ ?v1 )))):named a11 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(= (member$ ?v0 (poslsts$ ?v1 ))(and (member$ ?v0 (alllsts$ ?v1 ))(not (= ?v0 lNil$ ))))):named a12 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$a (lmember$ ?v0 )lNil$ )false ):pattern ((lmember$ ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ ))(=> (and (member$ ?v0 (alllsts$ ?v1 ))(and (=> (member$ ?v0 (finlsts$ ?v1 ))false )(=> (member$ ?v0 (inflsts$ ?v1 ))false )))false )):named a14 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$b (gen_lset$ ?v0 )lNil$ )?v0 ):pattern ((gen_lset$ ?v0 )))):named a15 ))
(check-sat )
;(get-unsat-core )
