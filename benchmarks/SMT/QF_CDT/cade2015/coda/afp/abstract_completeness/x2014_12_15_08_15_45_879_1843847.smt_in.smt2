;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Rule$ 0 )
(declare-sort Rule_set$ 0 )
(declare-sort Rule_bool_fun$ 0 )
(declare-codatatypes ()((Rule_stream$ (sCons$ (shd$ Rule$ )(stl$ Rule_stream$ )))))
(declare-fun bot$ ()Rule_set$ )
(declare-fun bot$a ()Rule_bool_fun$ )
(declare-fun bot$b ()Bool )
(declare-fun sset$ (Rule_stream$ )Rule_set$ )
(declare-fun rules$ ()Rule_stream$ )
(declare-fun member$ (Rule$ Rule_set$ )Bool )
(declare-fun collect$ (Rule_bool_fun$ )Rule_set$ )
(declare-fun fun_app$ (Rule_bool_fun$ Rule$ )Bool )
(declare-fun countable$ (Rule_set$ )Bool )
(assert (! (not (not (= (sset$ rules$ )bot$ ))):named a0 ))
(assert (! (countable$ (sset$ rules$ )):named a1 ))
(assert (! (forall ((?v0 Rule_bool_fun$ ))(= (= (collect$ ?v0 )bot$ )(forall ((?v1 Rule$ ))(not (fun_app$ ?v0 ?v1 ))))):named a2 ))
(assert (! (forall ((?v0 Rule_set$ ))(= (forall ((?v1 Rule$ ))(not (member$ ?v1 ?v0 )))(= ?v0 bot$ ))):named a3 ))
(assert (! (forall ((?v0 Rule_bool_fun$ ))(= (= bot$ (collect$ ?v0 ))(forall ((?v1 Rule$ ))(not (fun_app$ ?v0 ?v1 ))))):named a4 ))
(assert (! (forall ((?v0 Rule$ ))(= (member$ ?v0 bot$ )false )):named a5 ))
(assert (! (forall ((?v0 Rule$ ))(! (= (fun_app$ bot$a ?v0 )bot$b ):pattern ((fun_app$ bot$a ?v0 )))):named a6 ))
(assert (! (forall ((?v0 Rule_set$ ))(= (exists ((?v1 Rule$ ))(member$ ?v1 ?v0 ))(not (= ?v0 bot$ )))):named a7 ))
(assert (! (forall ((?v0 Rule_set$ ))(=> (forall ((?v1 Rule$ ))(=> (member$ ?v1 ?v0 )false ))(= ?v0 bot$ ))):named a8 ))
(assert (! (forall ((?v0 Rule_set$ )(?v1 Rule$ ))(=> (= ?v0 bot$ )(not (member$ ?v1 ?v0 )))):named a9 ))
(assert (! (forall ((?v0 Rule$ ))(=> (member$ ?v0 bot$ )false )):named a10 ))
(assert (! (forall ((?v0 Rule$ ))(! (= (fun_app$ bot$a ?v0 )bot$b ):pattern ((fun_app$ bot$a ?v0 )))):named a11 ))
(assert (! (= bot$ (collect$ bot$a )):named a12 ))
(assert (! (forall ((?v0 Rule_stream$ ))(countable$ (sset$ ?v0 ))):named a13 ))
(check-sat )
;(get-unsat-core )
