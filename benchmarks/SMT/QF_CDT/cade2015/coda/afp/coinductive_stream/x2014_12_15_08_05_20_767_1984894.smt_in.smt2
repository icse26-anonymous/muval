;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort Nat_a_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_stream$ (sCons$ (shd$ A$ )(stl$ A_stream$ )))))
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun n$ ()Nat$ )
(declare-fun xs$ ()A_list$ )
(declare-fun ys$ ()A_stream$ )
(declare-fun nth$ (A_list$ Nat$ )A$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun size$ (A_list$ )Nat$ )
(declare-fun snth$ (A_stream$ Nat$ )A$ )
(declare-fun minus$ (Nat$ Nat$ )Nat$ )
(declare-fun shift$ (A_list$ A_stream$ )A_stream$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$a (Nat_a_bool_fun_fun$ Nat$ )A_bool_fun$ )
(declare-fun fun_app$b (A_list_bool_fun$ A_list$ )Bool )
(assert (! (not (= (snth$ (shift$ xs$ ys$ )n$ )(ite (less$ n$ (size$ xs$ ))(nth$ xs$ n$ )(snth$ ys$ (minus$ n$ (size$ xs$ )))))):named a0 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list$ )(?v2 A_stream$ ))(=> (less$ ?v0 (size$ ?v1 ))(= (snth$ (shift$ ?v1 ?v2 )?v0 )(nth$ ?v1 ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_stream$ )(?v2 Nat$ ))(= (snth$ (shift$ ?v0 ?v1 )?v2 )(ite (less$ ?v2 (size$ ?v0 ))(nth$ ?v0 ?v2 )(snth$ ?v1 (minus$ ?v2 (size$ ?v0 )))))):named a2 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= ?v0 ?v1 )(and (= (size$ ?v0 )(size$ ?v1 ))(forall ((?v2 Nat$ ))(=> (less$ ?v2 (size$ ?v0 ))(= (nth$ ?v0 ?v2 )(nth$ ?v1 ?v2 ))))))):named a3 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_a_bool_fun_fun$ ))(= (forall ((?v2 Nat$ ))(=> (less$ ?v2 ?v0 )(exists ((?v3 A$ ))(fun_app$ (fun_app$a ?v1 ?v2 )?v3 ))))(exists ((?v2 A_list$ ))(and (= (size$ ?v2 )?v0 )(forall ((?v3 Nat$ ))(=> (less$ ?v3 ?v0 )(fun_app$ (fun_app$a ?v1 ?v3 )(nth$ ?v2 ?v3 )))))))):named a4 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (and (= (size$ ?v0 )(size$ ?v1 ))(forall ((?v2 Nat$ ))(=> (less$ ?v2 (size$ ?v0 ))(= (nth$ ?v0 ?v2 )(nth$ ?v1 ?v2 )))))(= ?v0 ?v1 ))):named a5 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_stream$ )(?v2 A_stream$ ))(= (= (shift$ ?v0 ?v1 )(shift$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a6 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (less$ ?v0 ?v1 )(less$ ?v0 ?v2 ))(less$ (minus$ ?v2 ?v1 )(minus$ ?v2 ?v0 )))):named a7 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (less$ ?v0 ?v1 )(less$ (minus$ ?v0 ?v2 )?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_list_bool_fun$ )(?v1 A_list$ ))(=> (forall ((?v2 A_list$ ))(=> (forall ((?v3 A_list$ ))(=> (less$ (size$ ?v3 )(size$ ?v2 ))(fun_app$b ?v0 ?v3 )))(fun_app$b ?v0 ?v2 )))(fun_app$b ?v0 ?v1 ))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 Nat$ ))(= (minus$ (minus$ ?v0 ?v1 )?v2 )(minus$ (minus$ ?v0 ?v2 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 Nat$ ))(not (less$ ?v0 ?v0 ))):named a11 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(=> (and (not (= ?v0 ?v1 ))(and (=> (less$ ?v0 ?v1 )false )(=> (less$ ?v1 ?v0 )false )))false )):named a12 ))
(check-sat )
;(get-unsat-core )
