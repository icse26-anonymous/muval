;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_set$ 0 )
(declare-sort A_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_llist_set$ 0 )
(declare-sort A_llist_llist_llist_bool_fun$ 0 )
(declare-sort A_llist_llist_llist_llist_set$ 0 )
(declare-sort A_llist$ 0)
(declare-sort A_llist_llist$ 0)
(declare-sort A_llist_llist_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun lNil$a ()A_llist_llist$)
(declare-fun lhd$a (A_llist_llist$)A_llist$)
(declare-fun ltl$a (A_llist_llist$)A_llist_llist$)
(declare-fun lCons$a (A_llist$ A_llist_llist$ )A_llist_llist$)
(declare-fun lNil$b ()A_llist_llist_llist$)
(declare-fun lhd$b (A_llist_llist_llist$)A_llist_llist$)
(declare-fun ltl$b (A_llist_llist_llist$)A_llist_llist_llist$)
(declare-fun lCons$b (A_llist_llist$ A_llist_llist_llist$ )A_llist_llist_llist$)
(declare-fun a$ ()A_set$ )
(declare-fun x$ ()A_llist$ )
(declare-fun y$ ()A_llist$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun collect$ (A_llist_llist_llist_bool_fun$ )A_llist_llist_llist_set$ )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun finpref$ (A_set$ A_llist$ )A_llist_set$ )
(declare-fun fpslsts$ (A_llist_llist_llist_set$ )A_llist_llist_llist_llist_set$ )
(declare-fun fun_app$ (A_llist_bool_fun$ A_llist$ )Bool )
(declare-fun inflsts$ (A_set$ )A_llist_set$ )
(declare-fun infsuff$ (A_llist_llist_set$ A_llist_llist_llist$ )A_llist_llist_llist_set$ )
(declare-fun less_eq$ (A_llist_set$ A_llist_set$ )Bool )
(declare-fun member$a (A_llist_llist_llist$ A_llist_llist_llist_set$ )Bool )
(declare-fun member$b (A$ A_set$ )Bool )
(declare-fun member$c (A_llist_llist$ A_llist_llist_set$ )Bool )
(declare-fun poslsts$ (A_llist_llist_llist_set$ )A_llist_llist_llist_llist_set$ )
(declare-fun collect$a (A_bool_fun$ )A_set$ )
(declare-fun collect$b (A_llist_llist_bool_fun$ )A_llist_llist_set$ )
(declare-fun collect$c (A_llist_bool_fun$ )A_llist_set$ )
(declare-fun finlsts$a (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun finlsts$b (A_llist_set$ )A_llist_llist_set$ )
(declare-fun finpref$a (A_llist_llist_set$ A_llist_llist_llist$ )A_llist_llist_llist_set$ )
(declare-fun finpref$b (A_llist_set$ A_llist_llist$ )A_llist_llist_set$ )
(declare-fun fpslsts$a (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun fpslsts$b (A_set$ )A_llist_set$ )
(declare-fun fpslsts$c (A_llist_set$ )A_llist_llist_set$ )
(declare-fun fun_app$a (A_llist_llist_llist_bool_fun$ A_llist_llist_llist$ )Bool )
(declare-fun fun_app$b (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$c (A_llist_llist_bool_fun$ A_llist_llist$ )Bool )
(declare-fun inflsts$a (A_llist_llist_llist_set$ )A_llist_llist_llist_llist_set$ )
(declare-fun inflsts$b (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun inflsts$c (A_llist_set$ )A_llist_llist_set$ )
(declare-fun infsuff$a (A_llist_set$ A_llist_llist$ )A_llist_llist_set$ )
(declare-fun infsuff$b (A_set$ A_llist$ )A_llist_set$ )
(declare-fun less_eq$a (A_llist_llist_llist_set$ A_llist_llist_llist_set$ )Bool )
(declare-fun less_eq$b (A_llist_llist_llist_llist_set$ A_llist_llist_llist_llist_set$ )Bool )
(declare-fun less_eq$c (A_llist_llist_set$ A_llist_llist_set$ )Bool )
(declare-fun less_eq$d (A_set$ A_set$ )Bool )
(declare-fun less_eq$e (A_llist$ )A_llist_bool_fun$ )
(declare-fun poslsts$a (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun poslsts$b (A_set$ )A_llist_set$ )
(declare-fun poslsts$c (A_llist_set$ )A_llist_llist_set$ )
(assert (! (not (and (member$ x$ (inflsts$ a$ ))(and (member$ y$ (inflsts$ a$ ))(less_eq$ (finpref$ a$ x$ )(finpref$ a$ y$ ))))):named a0 ))
(assert (! (member$ x$ (inflsts$ a$ )):named a1 ))
(assert (! (member$ y$ (inflsts$ a$ )):named a2 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(=> (less_eq$a ?v0 ?v1 )(less_eq$b (inflsts$a ?v0 )(inflsts$a ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (less_eq$c ?v0 ?v1 )(less_eq$a (inflsts$b ?v0 )(inflsts$b ?v1 )))):named a4 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (less_eq$ ?v0 ?v1 )(less_eq$c (inflsts$c ?v0 )(inflsts$c ?v1 )))):named a5 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (less_eq$d ?v0 ?v1 )(less_eq$ (inflsts$ ?v0 )(inflsts$ ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(=> (forall ((?v2 A_llist_llist_llist$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 )))(less_eq$a ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (forall ((?v2 A$ ))(=> (member$b ?v2 ?v0 )(member$b ?v2 ?v1 )))(less_eq$d ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (forall ((?v2 A_llist_llist$ ))(=> (member$c ?v2 ?v0 )(member$c ?v2 ?v1 )))(less_eq$c ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 )))(less_eq$ ?v0 ?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(=> (and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (and (less_eq$d ?v0 ?v1 )(less_eq$d ?v1 ?v0 ))(= ?v0 ?v1 ))):named a12 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (and (less_eq$c ?v0 ?v1 )(less_eq$c ?v1 ?v0 ))(= ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a14 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ ))(less_eq$a ?v0 ?v0 )):named a15 ))
(assert (! (forall ((?v0 A_set$ ))(less_eq$d ?v0 ?v0 )):named a16 ))
(assert (! (forall ((?v0 A_llist_llist_set$ ))(less_eq$c ?v0 ?v0 )):named a17 ))
(assert (! (forall ((?v0 A_llist_set$ ))(less_eq$ ?v0 ?v0 )):named a18 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (less_eq$e ?v0 )?v0 )):named a19 ))
(assert (! (forall ((?v0 A_llist$ ))(=> (and (member$ ?v0 (finlsts$ a$ ))(fun_app$ (less_eq$e ?v0 )x$ ))(fun_app$ (less_eq$e ?v0 )y$ ))):named a20 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(=> (less_eq$a ?v0 ?v1 )(less_eq$b (poslsts$ ?v0 )(poslsts$ ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (less_eq$c ?v0 ?v1 )(less_eq$a (poslsts$a ?v0 )(poslsts$a ?v1 )))):named a22 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (less_eq$d ?v0 ?v1 )(less_eq$ (poslsts$b ?v0 )(poslsts$b ?v1 )))):named a23 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (less_eq$ ?v0 ?v1 )(less_eq$c (poslsts$c ?v0 )(poslsts$c ?v1 )))):named a24 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist_llist$ ))(=> (and (member$a ?v0 (finpref$a ?v1 ?v2 ))(member$a ?v2 (inflsts$b ?v1 )))(member$a ?v2 (infsuff$ ?v1 ?v0 )))):named a25 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist_llist$ ))(=> (and (member$c ?v0 (finpref$b ?v1 ?v2 ))(member$c ?v2 (inflsts$c ?v1 )))(member$c ?v2 (infsuff$a ?v1 ?v0 )))):named a26 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_llist$ ))(=> (and (member$ ?v0 (finpref$ ?v1 ?v2 ))(member$ ?v2 (inflsts$ ?v1 )))(member$ ?v2 (infsuff$b ?v1 ?v0 )))):named a27 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(=> (less_eq$a ?v0 ?v1 )(less_eq$b (fpslsts$ ?v0 )(fpslsts$ ?v1 )))):named a28 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (less_eq$c ?v0 ?v1 )(less_eq$a (fpslsts$a ?v0 )(fpslsts$a ?v1 )))):named a29 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (less_eq$d ?v0 ?v1 )(less_eq$ (fpslsts$b ?v0 )(fpslsts$b ?v1 )))):named a30 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (less_eq$ ?v0 ?v1 )(less_eq$c (fpslsts$c ?v0 )(fpslsts$c ?v1 )))):named a31 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(= (= ?v0 ?v1 )(and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 )))):named a32 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (= ?v0 ?v1 )(and (less_eq$d ?v0 ?v1 )(less_eq$d ?v1 ?v0 )))):named a33 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(= (= ?v0 ?v1 )(and (less_eq$c ?v0 ?v1 )(less_eq$c ?v1 ?v0 )))):named a34 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(= (= ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 )))):named a35 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(= (less_eq$a ?v0 ?v1 )(forall ((?v2 A_llist_llist_llist$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 ))))):named a36 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (less_eq$d ?v0 ?v1 )(forall ((?v2 A$ ))(=> (member$b ?v2 ?v0 )(member$b ?v2 ?v1 ))))):named a37 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(= (less_eq$c ?v0 ?v1 )(forall ((?v2 A_llist_llist$ ))(=> (member$c ?v2 ?v0 )(member$c ?v2 ?v1 ))))):named a38 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(= (less_eq$ ?v0 ?v1 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 ))))):named a39 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(= (less_eq$a ?v0 ?v1 )(forall ((?v2 A_llist_llist_llist$ ))(=> (member$a ?v2 ?v0 )(member$a ?v2 ?v1 ))))):named a40 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (less_eq$d ?v0 ?v1 )(forall ((?v2 A$ ))(=> (member$b ?v2 ?v0 )(member$b ?v2 ?v1 ))))):named a41 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(= (less_eq$c ?v0 ?v1 )(forall ((?v2 A_llist_llist$ ))(=> (member$c ?v2 ?v0 )(member$c ?v2 ?v1 ))))):named a42 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(= (less_eq$ ?v0 ?v1 )(forall ((?v2 A_llist$ ))(=> (member$ ?v2 ?v0 )(member$ ?v2 ?v1 ))))):named a43 ))
(assert (! (forall ((?v0 A_llist_llist_llist_bool_fun$ )(?v1 A_llist_llist_llist_bool_fun$ ))(=> (forall ((?v2 A_llist_llist_llist$ ))(=> (fun_app$a ?v0 ?v2 )(fun_app$a ?v1 ?v2 )))(less_eq$a (collect$ ?v0 )(collect$ ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_bool_fun$ ))(=> (forall ((?v2 A$ ))(=> (fun_app$b ?v0 ?v2 )(fun_app$b ?v1 ?v2 )))(less_eq$d (collect$a ?v0 )(collect$a ?v1 )))):named a45 ))
(assert (! (forall ((?v0 A_llist_llist_bool_fun$ )(?v1 A_llist_llist_bool_fun$ ))(=> (forall ((?v2 A_llist_llist$ ))(=> (fun_app$c ?v0 ?v2 )(fun_app$c ?v1 ?v2 )))(less_eq$c (collect$b ?v0 )(collect$b ?v1 )))):named a46 ))
(assert (! (forall ((?v0 A_llist_bool_fun$ )(?v1 A_llist_bool_fun$ ))(=> (forall ((?v2 A_llist$ ))(=> (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 )))(less_eq$ (collect$c ?v0 )(collect$c ?v1 )))):named a47 ))
(assert (! (forall ((?v0 A_llist_llist_llist_set$ )(?v1 A_llist_llist_llist_set$ ))(=> (and (= ?v0 ?v1 )(=> (and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 ))false ))false )):named a48 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (and (= ?v0 ?v1 )(=> (and (less_eq$d ?v0 ?v1 )(less_eq$d ?v1 ?v0 ))false ))false )):named a49 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (and (= ?v0 ?v1 )(=> (and (less_eq$c ?v0 ?v1 )(less_eq$c ?v1 ?v0 ))false ))false )):named a50 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (and (= ?v0 ?v1 )(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))false ))false )):named a51 ))
(assert (! (forall ((?v0 A_llist$ ))(fun_app$ (less_eq$e ?v0 )?v0 )):named a52 ))
(assert (! (forall ((?v0 A_llist_llist_llist$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist_llist$ ))(=> (and (member$a ?v0 (finlsts$a ?v1 ))(member$a ?v2 (inflsts$b ?v1 )))(= (member$a ?v2 (finpref$a ?v1 ?v0 ))(member$a ?v0 (infsuff$ ?v1 ?v2 ))))):named a53 ))
(assert (! (forall ((?v0 A_llist_llist$ )(?v1 A_llist_set$ )(?v2 A_llist_llist$ ))(=> (and (member$c ?v0 (finlsts$b ?v1 ))(member$c ?v2 (inflsts$c ?v1 )))(= (member$c ?v2 (finpref$b ?v1 ?v0 ))(member$c ?v0 (infsuff$a ?v1 ?v2 ))))):named a54 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set$ )(?v2 A_llist$ ))(=> (and (member$ ?v0 (finlsts$ ?v1 ))(member$ ?v2 (inflsts$ ?v1 )))(= (member$ ?v2 (finpref$ ?v1 ?v0 ))(member$ ?v0 (infsuff$b ?v1 ?v2 ))))):named a55 ))
(check-sat )
;(get-unsat-core )
