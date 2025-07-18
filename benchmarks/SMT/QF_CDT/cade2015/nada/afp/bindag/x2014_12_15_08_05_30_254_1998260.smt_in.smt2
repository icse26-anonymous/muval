;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Nat$ 0 )
(declare-sort Ref$ 0 )
(declare-sort Ref_set$ 0 )
(declare-sort Ref_ref_fun$ 0 )
(declare-sort Dag_bool_fun$ 0 )
(declare-sort Ref_ref_ref_fun_fun$ 0 )
(declare-sort Ref_ref_ref_ref_fun_fun_fun$ 0 )
(declare-sort Dag$ 0)
(declare-fun tip$ ()Dag$)
(declare-fun select$ (Dag$)Dag$)
(declare-fun selecta$ (Dag$)Ref$)
(declare-fun selectb$ (Dag$)Dag$)
(declare-fun node$ (Dag$ Ref$ Dag$ )Dag$)
(declare-fun l$ ()Ref_ref_fun$ )
(declare-fun p$ ()Ref$ )
(declare-fun r$ ()Ref_ref_fun$ )
(declare-fun s$ ()Dag$ )
(declare-fun t$ ()Dag$ )
(declare-fun dag$ (Ref$ Ref_ref_fun$ Ref_ref_fun$ )Dag_bool_fun$ )
(declare-fun less$ (Dag$ Dag$ )Bool )
(declare-fun null$ ()Ref$ )
(declare-fun size$ (Dag$ )Nat$ )
(declare-fun less$a (Nat$ Nat$ )Bool )
(declare-fun member$ (Ref$ Ref_set$ )Bool )
(declare-fun set_of$ (Dag$ )Ref_set$ )
(declare-fun subdag$ (Dag$ Dag$ )Bool )
(declare-fun fun_app$ (Dag_bool_fun$ Dag$ )Bool )
(declare-fun fun_upd$ (Ref_ref_fun$ )Ref_ref_ref_ref_fun_fun_fun$ )
(declare-fun fun_app$a (Ref_ref_fun$ Ref$ )Ref$ )
(declare-fun fun_app$b (Ref_ref_ref_fun_fun$ Ref$ )Ref_ref_fun$ )
(declare-fun fun_app$c (Ref_ref_ref_ref_fun_fun_fun$ Ref$ )Ref_ref_ref_fun_fun$ )
(assert (! (not (exists ((?v0 Ref$ ))(fun_app$ (dag$ ?v0 l$ r$ )s$ ))):named a0 ))
(assert (! (fun_app$ (dag$ p$ l$ r$ )t$ ):named a1 ))
(assert (! (subdag$ t$ s$ ):named a2 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ )(?v3 Dag$ )(?v4 Dag$ ))(=> (and (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v3 )(fun_app$ (dag$ ?v0 ?v1 ?v2 )?v4 ))(= ?v3 ?v4 ))):named a3 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ )(?v3 Dag$ ))(=> (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v3 )(exists ((?v4 Dag$ ))(and (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v4 )(forall ((?v5 Dag$ ))(=> (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v5 )(= ?v5 ?v4 ))))))):named a4 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag$ ))(=> (and (subdag$ ?v0 ?v1 )(subdag$ ?v1 ?v2 ))(subdag$ ?v0 ?v2 ))):named a5 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ ))(=> (and (subdag$ ?v0 ?v1 )(subdag$ ?v1 ?v0 ))false )):named a6 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ ))(=> (subdag$ ?v0 ?v1 )(not (= ?v0 ?v1 )))):named a7 ))
(assert (! (forall ((?v0 Dag$ ))(! (= (subdag$ tip$ ?v0 )false ):pattern ((subdag$ tip$ ?v0 )))):named a8 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Ref$ )(?v2 Dag$ )(?v3 Dag$ ))(! (= (subdag$ (node$ ?v0 ?v1 ?v2 )?v3 )(or (= ?v3 ?v0 )(or (= ?v3 ?v2 )(or (subdag$ ?v0 ?v3 )(subdag$ ?v2 ?v3 ))))):pattern ((subdag$ (node$ ?v0 ?v1 ?v2 )?v3 )))):named a9 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Ref$ )(?v3 Dag$ ))(=> (subdag$ ?v0 (node$ ?v1 ?v2 ?v3 ))(and (subdag$ ?v0 ?v1 )(subdag$ ?v0 ?v3 )))):named a10 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ ))(! (= (less$ ?v0 ?v1 )(subdag$ ?v1 ?v0 )):pattern ((less$ ?v0 ?v1 )))):named a11 ))
(assert (! (forall ((?v0 Ref_ref_fun$ )(?v1 Ref_ref_fun$ )(?v2 Dag$ ))(= (fun_app$ (dag$ null$ ?v0 ?v1 )?v2 )(= ?v2 tip$ ))):named a12 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ )(?v3 Dag$ ))(=> (not (= ?v0 null$ ))(= (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v3 )(exists ((?v4 Dag$ )(?v5 Dag$ ))(and (= ?v3 (node$ ?v4 ?v0 ?v5 ))(and (fun_app$ (dag$ (fun_app$a ?v1 ?v0 )?v1 ?v2 )?v4 )(fun_app$ (dag$ (fun_app$a ?v2 ?v0 )?v1 ?v2 )?v5 ))))))):named a13 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ )(?v3 Dag$ ))(=> (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v3 )(not (member$ null$ (set_of$ ?v3 ))))):named a14 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ ))(! (= (fun_app$ (dag$ ?v0 ?v1 ?v2 )tip$ )(= ?v0 null$ )):pattern ((dag$ ?v0 ?v1 ?v2 )))):named a15 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ )(?v3 Dag$ )(?v4 Ref$ )(?v5 Dag$ ))(! (= (fun_app$ (dag$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v4 )(and (not (= ?v0 null$ ))(and (fun_app$ (dag$ (fun_app$a ?v1 ?v0 )?v1 ?v2 )?v3 )(fun_app$ (dag$ (fun_app$a ?v2 ?v0 )?v1 ?v2 )?v5 ))))):pattern ((fun_app$ (dag$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))))):named a16 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Dag$ ))(= (member$ ?v0 (set_of$ ?v1 ))(exists ((?v2 Dag$ )(?v3 Dag$ ))(or (= ?v1 (node$ ?v2 ?v0 ?v3 ))(subdag$ ?v1 (node$ ?v2 ?v0 ?v3 )))))):named a17 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ ))(=> (subdag$ ?v0 ?v1 )(less$a (size$ ?v1 )(size$ ?v0 )))):named a18 ))
(assert (! (forall ((?v0 Ref$ )(?v1 Ref_ref_fun$ )(?v2 Ref_ref_fun$ )(?v3 Dag$ )(?v4 Ref$ )(?v5 Ref$ ))(=> (and (fun_app$ (dag$ ?v0 ?v1 ?v2 )?v3 )(not (member$ ?v4 (set_of$ ?v3 ))))(fun_app$ (dag$ ?v0 (fun_app$b (fun_app$c (fun_upd$ ?v1 )?v4 )?v5 )?v2 )?v3 ))):named a19 ))
(check-sat )
;(get-unsat-core )
