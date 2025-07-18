;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_llist_set$ 0 )
(declare-sort A_set_a_set_fun$ 0 )
(declare-sort A_llist_a_set_fun$ 0 )
(declare-sort A_llist_llist_set$ 0 )
(declare-sort A_set_a_llist_fun$ 0 )
(declare-sort A_llist_a_llist_fun$ 0 )
(declare-sort A_llist_set_a_set_fun$ 0 )
(declare-sort A_set_a_llist_set_fun$ 0 )
(declare-sort A_llist_a_llist_set_fun$ 0 )
(declare-sort A_llist_llist_llist_set$ 0 )
(declare-sort A_llist_set_a_llist_fun$ 0 )
(declare-sort A_llist_set_a_llist_set_fun$ 0 )
(declare-sort A_llist_a_llist_llist_set_fun$ 0 )
(declare-sort A_llist$ 0)
(declare-fun lNil$ ()A_llist$)
(declare-fun lhd$ (A_llist$)A$)
(declare-fun ltl$ (A_llist$)A_llist$)
(declare-fun lCons$ (A$ A_llist$ )A_llist$)
(declare-fun a$ ()A_set$ )
(declare-fun r$ ()A_llist$ )
(declare-fun s$ ()A_llist$ )
(declare-fun member$ (A_llist$ A_llist_set$ )Bool )
(declare-fun finlsts$ (A_set$ )A_llist_set$ )
(declare-fun fun_app$ (A_llist_a_llist_fun$ A_llist$ )A_llist$ )
(declare-fun less_eq$ (A_llist$ A_llist$ )Bool )
(declare-fun finlsts$a (A_llist_llist_set$ )A_llist_llist_llist_set$ )
(declare-fun finlsts$b (A_llist_set$ )A_llist_llist_set$ )
(declare-fun fun_app$a (A_llist_a_set_fun$ A_llist$ )A_set$ )
(declare-fun fun_app$b (A_set_a_llist_fun$ A_set$ )A_llist$ )
(declare-fun fun_app$c (A_set_a_set_fun$ A_set$ )A_set$ )
(declare-fun fun_app$d (A_llist_a_llist_set_fun$ A_llist$ )A_llist_set$ )
(declare-fun fun_app$e (A_set_a_llist_set_fun$ A_set$ )A_llist_set$ )
(declare-fun fun_app$f (A_llist_set_a_llist_fun$ A_llist_set$ )A_llist$ )
(declare-fun fun_app$g (A_llist_set_a_set_fun$ A_llist_set$ )A_set$ )
(declare-fun fun_app$h (A_llist_set_a_llist_set_fun$ A_llist_set$ )A_llist_set$ )
(declare-fun fun_app$i (A_llist_a_llist_llist_set_fun$ A_llist$ )A_llist_llist_set$ )
(declare-fun less_eq$a (A_llist_llist_set$ A_llist_llist_set$ )Bool )
(declare-fun less_eq$b (A_set$ A_set$ )Bool )
(declare-fun less_eq$c (A_llist_set$ A_llist_set$ )Bool )
(declare-fun less_eq$d (A_llist_llist_llist_set$ A_llist_llist_llist_set$ )Bool )
(assert (! (not (member$ r$ (finlsts$ a$ ))):named a0 ))
(assert (! (less_eq$ r$ s$ ):named a1 ))
(assert (! (member$ s$ (finlsts$ a$ )):named a2 ))
(assert (! (forall ((?v0 A_llist$ ))(less_eq$ ?v0 ?v0 )):named a3 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 ))(= ?v0 ?v1 ))):named a4 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v2 ))(less_eq$ ?v0 ?v2 ))):named a5 ))
(assert (! (forall ((?v0 A_llist_llist_set$ ))(less_eq$a ?v0 ?v0 )):named a6 ))
(assert (! (forall ((?v0 A_set$ ))(less_eq$b ?v0 ?v0 )):named a7 ))
(assert (! (forall ((?v0 A_llist_set$ ))(less_eq$c ?v0 ?v0 )):named a8 ))
(assert (! (forall ((?v0 A_llist$ ))(less_eq$ ?v0 ?v0 )):named a9 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(= (= ?v0 ?v1 )(and (less_eq$a ?v0 ?v1 )(less_eq$a ?v1 ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (= ?v0 ?v1 )(and (less_eq$b ?v0 ?v1 )(less_eq$b ?v1 ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(= (= ?v0 ?v1 )(and (less_eq$c ?v0 ?v1 )(less_eq$c ?v1 ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(= (= ?v0 ?v1 )(and (less_eq$ ?v0 ?v1 )(less_eq$ ?v1 ?v0 )))):named a13 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_a_llist_fun$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (= ?v0 (fun_app$ ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$ (fun_app$ ?v1 ?v4 )(fun_app$ ?v1 ?v5 ))))))(less_eq$ ?v0 (fun_app$ ?v1 ?v3 )))):named a14 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_llist_a_set_fun$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (= ?v0 (fun_app$a ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$b (fun_app$a ?v1 ?v4 )(fun_app$a ?v1 ?v5 ))))))(less_eq$b ?v0 (fun_app$a ?v1 ?v3 )))):named a15 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_set_a_llist_fun$ )(?v2 A_set$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$b ?v1 ?v2 ))(and (less_eq$b ?v2 ?v3 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (less_eq$b ?v4 ?v5 )(less_eq$ (fun_app$b ?v1 ?v4 )(fun_app$b ?v1 ?v5 ))))))(less_eq$ ?v0 (fun_app$b ?v1 ?v3 )))):named a16 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set_a_set_fun$ )(?v2 A_set$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$c ?v1 ?v2 ))(and (less_eq$b ?v2 ?v3 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (less_eq$b ?v4 ?v5 )(less_eq$b (fun_app$c ?v1 ?v4 )(fun_app$c ?v1 ?v5 ))))))(less_eq$b ?v0 (fun_app$c ?v1 ?v3 )))):named a17 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_a_llist_set_fun$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (= ?v0 (fun_app$d ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$c (fun_app$d ?v1 ?v4 )(fun_app$d ?v1 ?v5 ))))))(less_eq$c ?v0 (fun_app$d ?v1 ?v3 )))):named a18 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_set_a_llist_set_fun$ )(?v2 A_set$ )(?v3 A_set$ ))(=> (and (= ?v0 (fun_app$e ?v1 ?v2 ))(and (less_eq$b ?v2 ?v3 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (less_eq$b ?v4 ?v5 )(less_eq$c (fun_app$e ?v1 ?v4 )(fun_app$e ?v1 ?v5 ))))))(less_eq$c ?v0 (fun_app$e ?v1 ?v3 )))):named a19 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist_set_a_llist_fun$ )(?v2 A_llist_set$ )(?v3 A_llist_set$ ))(=> (and (= ?v0 (fun_app$f ?v1 ?v2 ))(and (less_eq$c ?v2 ?v3 )(forall ((?v4 A_llist_set$ )(?v5 A_llist_set$ ))(=> (less_eq$c ?v4 ?v5 )(less_eq$ (fun_app$f ?v1 ?v4 )(fun_app$f ?v1 ?v5 ))))))(less_eq$ ?v0 (fun_app$f ?v1 ?v3 )))):named a20 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_llist_set_a_set_fun$ )(?v2 A_llist_set$ )(?v3 A_llist_set$ ))(=> (and (= ?v0 (fun_app$g ?v1 ?v2 ))(and (less_eq$c ?v2 ?v3 )(forall ((?v4 A_llist_set$ )(?v5 A_llist_set$ ))(=> (less_eq$c ?v4 ?v5 )(less_eq$b (fun_app$g ?v1 ?v4 )(fun_app$g ?v1 ?v5 ))))))(less_eq$b ?v0 (fun_app$g ?v1 ?v3 )))):named a21 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set_a_llist_set_fun$ )(?v2 A_llist_set$ )(?v3 A_llist_set$ ))(=> (and (= ?v0 (fun_app$h ?v1 ?v2 ))(and (less_eq$c ?v2 ?v3 )(forall ((?v4 A_llist_set$ )(?v5 A_llist_set$ ))(=> (less_eq$c ?v4 ?v5 )(less_eq$c (fun_app$h ?v1 ?v4 )(fun_app$h ?v1 ?v5 ))))))(less_eq$c ?v0 (fun_app$h ?v1 ?v3 )))):named a22 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_a_llist_llist_set_fun$ )(?v2 A_llist$ )(?v3 A_llist$ ))(=> (and (= ?v0 (fun_app$i ?v1 ?v2 ))(and (less_eq$ ?v2 ?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$a (fun_app$i ?v1 ?v4 )(fun_app$i ?v1 ?v5 ))))))(less_eq$a ?v0 (fun_app$i ?v1 ?v3 )))):named a23 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ )(?v2 A_llist_llist_set$ ))(=> (and (= ?v0 ?v1 )(less_eq$a ?v1 ?v2 ))(less_eq$a ?v0 ?v2 ))):named a24 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set$ ))(=> (and (= ?v0 ?v1 )(less_eq$b ?v1 ?v2 ))(less_eq$b ?v0 ?v2 ))):named a25 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ )(?v2 A_llist_set$ ))(=> (and (= ?v0 ?v1 )(less_eq$c ?v1 ?v2 ))(less_eq$c ?v0 ?v2 ))):named a26 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist$ ))(=> (and (= ?v0 ?v1 )(less_eq$ ?v1 ?v2 ))(less_eq$ ?v0 ?v2 ))):named a27 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (= ?v0 ?v1 )(less_eq$a ?v0 ?v1 ))):named a28 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (= ?v0 ?v1 )(less_eq$b ?v0 ?v1 ))):named a29 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (= ?v0 ?v1 )(less_eq$c ?v0 ?v1 ))):named a30 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ ))(=> (= ?v0 ?v1 )(less_eq$ ?v0 ?v1 ))):named a31 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist_a_llist_fun$ )(?v3 A_llist$ ))(=> (and (less_eq$ ?v0 ?v1 )(and (= (fun_app$ ?v2 ?v1 )?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$ (fun_app$ ?v2 ?v4 )(fun_app$ ?v2 ?v5 ))))))(less_eq$ (fun_app$ ?v2 ?v0 )?v3 ))):named a32 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist_a_set_fun$ )(?v3 A_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(and (= (fun_app$a ?v2 ?v1 )?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$b (fun_app$a ?v2 ?v4 )(fun_app$a ?v2 ?v5 ))))))(less_eq$b (fun_app$a ?v2 ?v0 )?v3 ))):named a33 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set_a_llist_fun$ )(?v3 A_llist$ ))(=> (and (less_eq$b ?v0 ?v1 )(and (= (fun_app$b ?v2 ?v1 )?v3 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (less_eq$b ?v4 ?v5 )(less_eq$ (fun_app$b ?v2 ?v4 )(fun_app$b ?v2 ?v5 ))))))(less_eq$ (fun_app$b ?v2 ?v0 )?v3 ))):named a34 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set_a_set_fun$ )(?v3 A_set$ ))(=> (and (less_eq$b ?v0 ?v1 )(and (= (fun_app$c ?v2 ?v1 )?v3 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (less_eq$b ?v4 ?v5 )(less_eq$b (fun_app$c ?v2 ?v4 )(fun_app$c ?v2 ?v5 ))))))(less_eq$b (fun_app$c ?v2 ?v0 )?v3 ))):named a35 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist_a_llist_set_fun$ )(?v3 A_llist_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(and (= (fun_app$d ?v2 ?v1 )?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$c (fun_app$d ?v2 ?v4 )(fun_app$d ?v2 ?v5 ))))))(less_eq$c (fun_app$d ?v2 ?v0 )?v3 ))):named a36 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set_a_llist_set_fun$ )(?v3 A_llist_set$ ))(=> (and (less_eq$b ?v0 ?v1 )(and (= (fun_app$e ?v2 ?v1 )?v3 )(forall ((?v4 A_set$ )(?v5 A_set$ ))(=> (less_eq$b ?v4 ?v5 )(less_eq$c (fun_app$e ?v2 ?v4 )(fun_app$e ?v2 ?v5 ))))))(less_eq$c (fun_app$e ?v2 ?v0 )?v3 ))):named a37 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ )(?v2 A_llist_set_a_llist_fun$ )(?v3 A_llist$ ))(=> (and (less_eq$c ?v0 ?v1 )(and (= (fun_app$f ?v2 ?v1 )?v3 )(forall ((?v4 A_llist_set$ )(?v5 A_llist_set$ ))(=> (less_eq$c ?v4 ?v5 )(less_eq$ (fun_app$f ?v2 ?v4 )(fun_app$f ?v2 ?v5 ))))))(less_eq$ (fun_app$f ?v2 ?v0 )?v3 ))):named a38 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ )(?v2 A_llist_set_a_set_fun$ )(?v3 A_set$ ))(=> (and (less_eq$c ?v0 ?v1 )(and (= (fun_app$g ?v2 ?v1 )?v3 )(forall ((?v4 A_llist_set$ )(?v5 A_llist_set$ ))(=> (less_eq$c ?v4 ?v5 )(less_eq$b (fun_app$g ?v2 ?v4 )(fun_app$g ?v2 ?v5 ))))))(less_eq$b (fun_app$g ?v2 ?v0 )?v3 ))):named a39 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ )(?v2 A_llist_set_a_llist_set_fun$ )(?v3 A_llist_set$ ))(=> (and (less_eq$c ?v0 ?v1 )(and (= (fun_app$h ?v2 ?v1 )?v3 )(forall ((?v4 A_llist_set$ )(?v5 A_llist_set$ ))(=> (less_eq$c ?v4 ?v5 )(less_eq$c (fun_app$h ?v2 ?v4 )(fun_app$h ?v2 ?v5 ))))))(less_eq$c (fun_app$h ?v2 ?v0 )?v3 ))):named a40 ))
(assert (! (forall ((?v0 A_llist$ )(?v1 A_llist$ )(?v2 A_llist_a_llist_llist_set_fun$ )(?v3 A_llist_llist_set$ ))(=> (and (less_eq$ ?v0 ?v1 )(and (= (fun_app$i ?v2 ?v1 )?v3 )(forall ((?v4 A_llist$ )(?v5 A_llist$ ))(=> (less_eq$ ?v4 ?v5 )(less_eq$a (fun_app$i ?v2 ?v4 )(fun_app$i ?v2 ?v5 ))))))(less_eq$a (fun_app$i ?v2 ?v0 )?v3 ))):named a41 ))
(assert (! (forall ((?v0 A_llist_llist_set$ )(?v1 A_llist_llist_set$ ))(=> (less_eq$a ?v0 ?v1 )(less_eq$d (finlsts$a ?v0 )(finlsts$a ?v1 )))):named a42 ))
(assert (! (forall ((?v0 A_llist_set$ )(?v1 A_llist_set$ ))(=> (less_eq$c ?v0 ?v1 )(less_eq$a (finlsts$b ?v0 )(finlsts$b ?v1 )))):named a43 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(=> (less_eq$b ?v0 ?v1 )(less_eq$c (finlsts$ ?v0 )(finlsts$ ?v1 )))):named a44 ))
(assert (! (forall ((?v0 A_llist_llist_set$ ))(less_eq$a ?v0 ?v0 )):named a45 ))
(assert (! (forall ((?v0 A_set$ ))(less_eq$b ?v0 ?v0 )):named a46 ))
(assert (! (forall ((?v0 A_llist_set$ ))(less_eq$c ?v0 ?v0 )):named a47 ))
(assert (! (forall ((?v0 A_llist$ ))(less_eq$ ?v0 ?v0 )):named a48 ))
(check-sat )
;(get-unsat-core )
