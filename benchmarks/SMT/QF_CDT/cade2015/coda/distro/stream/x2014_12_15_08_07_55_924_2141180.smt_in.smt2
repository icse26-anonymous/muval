;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_stream_bool_fun$ 0 )
(declare-sort A_a_stream_bool_fun_fun$ 0 )
(declare-sort A_stream_a_stream_bool_fun_fun$ 0 )
(declare-codatatypes ()((A_stream$ (sCons$ (shd$ A$ )(stl$ A_stream$ )))))
(declare-fun s$ ()A_stream$ )
(declare-fun x$ ()A$ )
(declare-fun id$ ()A_a_fun$ )
(declare-fun sa$ ()A_stream$ )
(declare-fun bot$ ()A_set$ )
(declare-fun sset$ (A_stream$ )A_set$ )
(declare-fun insert$ (A$ A_set$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun fun_app$ (A_a_fun$ A$ )A$ )
(declare-fun less_eq$ (A_set$ A_set$ )Bool )
(declare-fun fun_app$a (A_stream_bool_fun$ A_stream$ )Bool )
(declare-fun fun_app$b (A_a_stream_bool_fun_fun$ A$ )A_stream_bool_fun$ )
(declare-fun fun_app$c (A_stream_a_stream_bool_fun_fun$ A_stream$ )A_stream_bool_fun$ )
(declare-fun siterate$ (A_a_fun$ A$ )A_stream$ )
(assert (! (not (and (= (shd$ sa$ )(shd$ (siterate$ id$ x$ )))(exists ((?v0 A_stream$ ))(and (= (stl$ sa$ )?v0 )(and (= (stl$ (siterate$ id$ x$ ))(siterate$ id$ x$ ))(= (sset$ ?v0 )(insert$ x$ bot$ ))))))):named a0 ))
(assert (! (= (shd$ sa$ )x$ ):named a1 ))
(assert (! (= (sset$ (stl$ sa$ ))(insert$ x$ bot$ )):named a2 ))
(assert (! (= (sset$ s$ )(insert$ x$ bot$ )):named a3 ))
(assert (! (= (sset$ sa$ )(insert$ x$ bot$ )):named a4 ))
(assert (! (forall ((?v0 A$ ))(= (sset$ (siterate$ id$ ?v0 ))(insert$ ?v0 bot$ ))):named a5 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (stl$ (siterate$ ?v0 ?v1 ))(siterate$ ?v0 (fun_app$ ?v0 ?v1 )))):named a6 ))
(assert (! (forall ((?v0 A_a_fun$ )(?v1 A$ ))(= (shd$ (siterate$ ?v0 ?v1 ))?v1 )):named a7 ))
(assert (! (forall ((?v0 A_stream$ )(?v1 A_stream$ ))(=> (and (= (shd$ ?v0 )(shd$ ?v1 ))(= (stl$ ?v0 )(stl$ ?v1 )))(= ?v0 ?v1 ))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ ))(=> (member$ ?v0 (sset$ (stl$ ?v1 )))(member$ ?v0 (sset$ ?v1 )))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A_stream$ )(?v2 A_a_stream_bool_fun_fun$ ))(=> (and (member$ ?v0 (sset$ ?v1 ))(and (forall ((?v3 A_stream$ ))(fun_app$a (fun_app$b ?v2 (shd$ ?v3 ))?v3 ))(forall ((?v3 A_stream$ )(?v4 A$ ))(=> (and (member$ ?v4 (sset$ (stl$ ?v3 )))(fun_app$a (fun_app$b ?v2 ?v4 )(stl$ ?v3 )))(fun_app$a (fun_app$b ?v2 ?v4 )?v3 )))))(fun_app$a (fun_app$b ?v2 ?v0 )?v1 ))):named a10 ))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(=> (and (fun_app$a (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 A_stream$ )(?v4 A_stream$ ))(=> (fun_app$a (fun_app$c ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(or (fun_app$a (fun_app$c ?v0 (stl$ ?v3 ))(stl$ ?v4 ))(= (stl$ ?v3 )(stl$ ?v4 )))))))(= ?v1 ?v2 ))):named a11 ))
(assert (! (forall ((?v0 A_stream_a_stream_bool_fun_fun$ )(?v1 A_stream$ )(?v2 A_stream$ ))(=> (and (fun_app$a (fun_app$c ?v0 ?v1 )?v2 )(forall ((?v3 A_stream$ )(?v4 A_stream$ ))(=> (fun_app$a (fun_app$c ?v0 ?v3 )?v4 )(and (= (shd$ ?v3 )(shd$ ?v4 ))(fun_app$a (fun_app$c ?v0 (stl$ ?v3 ))(stl$ ?v4 ))))))(= ?v1 ?v2 ))):named a12 ))
(assert (! (forall ((?v0 A_stream$ ))(member$ (shd$ ?v0 )(sset$ ?v0 ))):named a13 ))
(assert (! (less_eq$ (sset$ (stl$ sa$ ))(insert$ x$ bot$ )):named a14 ))
(assert (! (forall ((?v0 A$ ))(member$ ?v0 (insert$ ?v0 bot$ ))):named a15 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$ id$ ?v0 )?v0 ):pattern ((fun_app$ id$ ?v0 )))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ ))(= (insert$ ?v0 (insert$ ?v0 ?v1 ))(insert$ ?v0 ?v1 ))):named a17 ))
(check-sat )
;(get-unsat-core )
