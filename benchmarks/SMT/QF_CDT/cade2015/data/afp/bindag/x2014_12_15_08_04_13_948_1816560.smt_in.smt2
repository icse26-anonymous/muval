;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort Ref$ 0 )
(declare-sort Dag_dag_fun$ 0 )
(declare-datatypes ()((Dag$ (tip$ )(node$ (select$ Dag$ )(selecta$ Ref$ )(selectb$ Dag$ )))))
(declare-fun x$ ()Dag$ )
(declare-fun y$ ()Dag$ )
(declare-fun dag$ (Dag$ )Bool )
(declare-fun less$ (Dag$ Dag$ )Bool )
(declare-fun fun_app$ (Dag_dag_fun$ Dag$ )Dag$ )
(assert (! (not (dag$ x$ )):named a0 ))
(assert (! (dag$ y$ ):named a1 ))
(assert (! (less$ x$ y$ ):named a2 ))
(assert (! (= (dag$ tip$ )true ):named a3 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag_dag_fun$ )(?v2 Dag$ )(?v3 Dag$ ))(=> (and (= ?v0 (fun_app$ ?v1 ?v2 ))(and (less$ ?v2 ?v3 )(forall ((?v4 Dag$ )(?v5 Dag$ ))(=> (less$ ?v4 ?v5 )(less$ (fun_app$ ?v1 ?v4 )(fun_app$ ?v1 ?v5 ))))))(less$ ?v0 (fun_app$ ?v1 ?v3 )))):named a4 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag$ ))(=> (and (= ?v0 ?v1 )(less$ ?v1 ?v2 ))(less$ ?v0 ?v2 ))):named a5 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ ))(=> (and (less$ ?v0 ?v1 )(=> (not false )(less$ ?v1 ?v0 )))false )):named a6 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag_dag_fun$ )(?v3 Dag$ ))(=> (and (less$ ?v0 ?v1 )(and (= (fun_app$ ?v2 ?v1 )?v3 )(forall ((?v4 Dag$ )(?v5 Dag$ ))(=> (less$ ?v4 ?v5 )(less$ (fun_app$ ?v2 ?v4 )(fun_app$ ?v2 ?v5 ))))))(less$ (fun_app$ ?v2 ?v0 )?v3 ))):named a7 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag$ ))(=> (and (less$ ?v0 ?v1 )(= ?v1 ?v2 ))(less$ ?v0 ?v2 ))):named a8 ))
(assert (! (forall ((?v0 Dag$ )(?v1 Dag$ )(?v2 Dag_dag_fun$ )(?v3 Dag$ ))(=> (and (less$ ?v0 ?v1 )(and (less$ (fun_app$ ?v2 ?v1 )?v3 )(forall ((?v4 Dag$ )(?v5 Dag$ ))(=> (less$ ?v4 ?v5 )(less$ (fun_app$ ?v2 ?v4 )(fun_app$ ?v2 ?v5 ))))))(less$ (fun_app$ ?v2 ?v0 )?v3 ))):named a9 ))
(assert (! (forall ((?v0 Dag$ ))(not (less$ ?v0 tip$ ))):named a10 ))
(assert (! (forall ((?v0 Dag$ ))(not (less$ ?v0 ?v0 ))):named a11 ))
(assert (! (forall ((?v0 Dag$ ))(not (less$ ?v0 ?v0 ))):named a12 ))
(check-sat )
;(get-unsat-core )
