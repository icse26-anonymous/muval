;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_list_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_stream_a_stream_bool_fun_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun s$ ()A_stream$ )
(declare-fun xs$ ()A_list$ )
(declare-fun bind$ (A_list$ A_a_list_fun$ )A_list$ )
(declare-fun smap$ (A_a_fun$ A_stream$ )A_stream$ )
(declare-fun sset$ (A_stream$ )A_set$ )
(declare-fun shift$ (A_list$ A_stream$ )A_stream$ )
(declare-fun append$ (A_list$ A_list$ )A_list$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun fun_app$a (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$b (A_stream_a_stream_bool_fun_fun$ A_stream$ )A_stream_bool_fun$ )
(declare-fun fun_app$c (A_bool_fun$ A$ )Bool )
(declare-fun dropWhile$ (A_bool_fun$ A_list$ )A_list$ )
(assert (! (not (= (shd$ (shift$ xs$ s$ ))(ite (= xs$ nil$ )(shd$ s$ )(hd$ xs$ )))):named a0 ))
(assert (! (forall ((?v0 A_stream$ ))(! (= (shift$ nil$ ?v0 )?v0 ):pattern ((shift$ nil$ ?v0 )))):named a1 ))
(assert (! (forall ((?v0 A_list$ ))(=> (and (=> (= ?v0 nil$ )false )(=> (not (= ?v0 nil$ ))false ))false )):named a2 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A_stream$ ))(= (shd$ (smap$ ?v0 ?v1 ))(fun_app$ ?v0 (shd$ ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_stream$ ))(= (shift$ (append$ ?v0 ?v1 )?v2 )(shift$ ?v0 (shift$ ?v1 ?v2 )))):named a4 ))
(assert (! (forall ((?v0 A_stream$ ))(member$ (shd$ ?v0 )(sset$ ?v0 ))):named a5 ))
(assert (! (forall ((?v0 A_a_list_fun$ ))(! (= (bind$ nil$ ?v0 )nil$ ):pattern ((bind$ nil$ ?v0 )))):named a6 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(=> (and (= (shd$ ?v0 )(shd$ ?v1 ))(= (stl$ ?v0 )(stl$ ?v1 )))(= ?v0 ?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(=> (and (fun_app$a (fun_app$b ?v0 ?v1 )?v2 )(forall ((?v3 A_stream$ )(?v4 A_stream$ ))(=> (fun_app$a (fun_app$b ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(or (fun_app$a (fun_app$b ?v0 (stl$ ?v3 ))(stl$ ?v4 ))(= (stl$ ?v3 )(stl$ ?v4 )))))))(= ?v1 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(=> (and (fun_app$a (fun_app$b ?v0 ?v1 )?v2 )(forall ((?v3 A_stream$ )(?v4 A_stream$ ))(=> (fun_app$a (fun_app$b ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(fun_app$a (fun_app$b ?v0 (stl$ ?v3 ))(stl$ ?v4 ))))))(= ?v1 ?v2 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (shd$ (sCons$ ?v0 ?v1 ))?v0 ):pattern ((sCons$ ?v0 ?v1 )))):named a10 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (not (= ?v0 nil$ ))(= (hd$ (append$ ?v0 ?v1 ))(hd$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_list$ ))(=> (not (= (dropWhile$ ?v0 ?v1 )nil$ ))(not (fun_app$c ?v0 (hd$ (dropWhile$ ?v0 ?v1 )))))):named a12 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v0 ?v2 ))(= ?v1 ?v2 ))):named a13 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (= (append$ ?v0 ?v1 )(append$ ?v2 ?v1 ))(= ?v0 ?v2 ))):named a14 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ )(?v2 A_list$ ))(= (append$ (append$ ?v0 ?v1 )?v2 )(append$ ?v0 (append$ ?v1 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_list$ ))(= (dropWhile$ ?v0 (dropWhile$ ?v0 ?v1 ))(dropWhile$ ?v0 ?v1 ))):named a16 ))
(check-sat )
;(get-unsat-core )
