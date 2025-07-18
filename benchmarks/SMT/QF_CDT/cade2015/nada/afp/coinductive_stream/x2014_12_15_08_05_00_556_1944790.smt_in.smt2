;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_stream$ 0)
(declare-fun shd$ (A_stream$)A$)
(declare-fun stl$ (A_stream$)A_stream$)
(declare-fun sCons$ (A$ A_stream$ )A_stream$)
(declare-fun xs$ ()A_stream$ )
(declare-fun bot$ ()A_set$ )
(declare-fun bot$a ()A_bool_fun$ )
(declare-fun bot$b ()Bool )
(declare-fun sset$ (A_stream$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun collect$ (A_bool_fun$ )A_set$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun smember$ (A$ A_stream$ )Bool )
(declare-fun is_empty$ (A_set$ )Bool )
(assert (! (not (not (= (sset$ xs$ )bot$ ))):named a0 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(= (= (collect$ ?v0 )bot$ )(forall ((?v1 A$ ))(not (fun_app$ ?v0 ?v1 ))))):named a1 ))
(assert (! (forall ((?v0 A_set$ ))(= (forall ((?v1 A$ ))(not (member$ ?v1 ?v0 )))(= ?v0 bot$ ))):named a2 ))
(assert (! (forall ((?v0 A_bool_fun$ ))(= (= bot$ (collect$ ?v0 ))(forall ((?v1 A$ ))(not (fun_app$ ?v0 ?v1 ))))):named a3 ))
(assert (! (forall ((?v0 A$ ))(= (member$ ?v0 bot$ )false )):named a4 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ bot$a ?v0 )bot$b ):pattern ((fun_app$ bot$a ?v0 )))):named a5 ))
(assert (! (forall ((?v0 A_set$ ))(= (exists ((?v1 A$ ))(member$ ?v1 ?v0 ))(not (= ?v0 bot$ )))):named a6 ))
(assert (! (forall ((?v0 A_set$ ))(=> (forall ((?v1 A$ ))(=> (member$ ?v1 ?v0 )false ))(= ?v0 bot$ ))):named a7 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A$ ))(=> (= ?v0 bot$ )(not (member$ ?v1 ?v0 )))):named a8 ))
(assert (! (forall ((?v0 A$ ))(=> (member$ ?v0 bot$ )false )):named a9 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ bot$a ?v0 )bot$b ):pattern ((fun_app$ bot$a ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(! (= (smember$ ?v0 ?v1 )(member$ ?v0 (sset$ ?v1 ))):pattern ((smember$ ?v0 ?v1 )))):named a11 ))
(assert (! (= bot$ (collect$ bot$a )):named a12 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (is_empty$ ?v0 )(= ?v0 bot$ )):pattern ((is_empty$ ?v0 )))):named a13 ))
(check-sat )
;(get-unsat-core )
