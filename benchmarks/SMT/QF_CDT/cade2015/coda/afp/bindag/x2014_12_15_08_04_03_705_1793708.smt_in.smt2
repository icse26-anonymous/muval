;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Ref$ 0 )
(declare-sort Dag_dag_fun$ 0 )
(declare-sort Dag$ 0)
(declare-fun tip$ ()Dag$)
(declare-fun select$ (Dag$)Dag$)
(declare-fun selecta$ (Dag$)Ref$)
(declare-fun selectb$ (Dag$)Dag$)
(declare-fun node$ (Dag$ Ref$ Dag$ )Dag$)
(declare-fun a$ ()Ref$ )
(declare-fun l$ ()Dag$ )
(declare-fun r$ ()Dag$ )
(declare-fun x$ ()Dag$ )
(declare-fun less$ (Dag$ Dag$ )Bool )
(declare-fun fun_app$ (Dag_dag_fun$ Dag$ )Dag$ )
(assert (! (not (and (less$ l$ x$ )(less$ r$ x$ ))):named a0 ))
(assert (! (less$ (node$ l$ a$ r$ )x$ ):named a1 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Ref$ )(?v2 Dag$ )(?v3 Dag$ )(?v4 Ref$ )(?v5 Dag$ ))(= (= (node$ ?v0 ?v1 ?v2 )(node$ ?v3 ?v4 ?v5 ))(and (= ?v0 ?v3 )(and (= ?v1 ?v4 )(= ?v2 ?v5 ))))):named a2 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Ref$ )(?v3 Dag$ ))(! (= (less$ ?v0 (node$ ?v1 ?v2 ?v3 ))(or (= ?v0 ?v1 )(or (= ?v0 ?v3 )(or (less$ ?v0 ?v1 )(less$ ?v0 ?v3 ))))):pattern ((less$ ?v0 (node$ ?v1 ?v2 ?v3 ))))):named a3 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag_dag_fun$ )(?v2 Dag$ )(?v3 Dag$ ))(=> (and (= ?v0 (fun_app$ ?v1 ?v2 ))(and (less$ ?v2 ?v3 )(forall ((?v4 Dag$ )(?v5 Dag$ ))(=> (less$ ?v4 ?v5 )(less$ (fun_app$ ?v1 ?v4 )(fun_app$ ?v1 ?v5 ))))))(less$ ?v0 (fun_app$ ?v1 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag$ ))(=> (and (= ?v0 ?v1 )(less$ ?v1 ?v2 ))(less$ ?v0 ?v2 ))):named a5 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ ))(=> (and (less$ ?v0 ?v1 )(=> (not false )(less$ ?v1 ?v0 )))false )):named a6 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag_dag_fun$ )(?v3 Dag$ ))(=> (and (less$ ?v0 ?v1 )(and (= (fun_app$ ?v2 ?v1 )?v3 )(forall ((?v4 Dag$ )(?v5 Dag$ ))(=> (less$ ?v4 ?v5 )(less$ (fun_app$ ?v2 ?v4 )(fun_app$ ?v2 ?v5 ))))))(less$ (fun_app$ ?v2 ?v0 )?v3 ))):named a7 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag$ ))(=> (and (less$ ?v0 ?v1 )(= ?v1 ?v2 ))(less$ ?v0 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag_dag_fun$ )(?v3 Dag$ ))(=> (and (less$ ?v0 ?v1 )(and (less$ (fun_app$ ?v2 ?v1 )?v3 )(forall ((?v4 Dag$ )(?v5 Dag$ ))(=> (less$ ?v4 ?v5 )(less$ (fun_app$ ?v2 ?v4 )(fun_app$ ?v2 ?v5 ))))))(less$ (fun_app$ ?v2 ?v0 )?v3 ))):named a9 ))
(assert (! (forall ((?v0 Dag$ ))(not (less$ ?v0 ?v0 ))):named a10 ))
(assert (! (forall ((?v0 Dag$ ))(not (less$ ?v0 ?v0 ))):named a11 ))
(check-sat )
;(get-unsat-core )
