;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_list_bool_fun$ 0 )
(declare-sort Nat_a_bool_fun_fun$ 0 )
(declare-datatypes ()((A_list$ (nil$ )(cons$ (hd$ A$ )(tl$ A_list$ )))))
(declare-fun m$ ()Nat$ )
(declare-fun n$ ()Nat$ )
(declare-fun p$ ()A_bool_fun$ )
(declare-fun x$ ()A$ )
(declare-fun xs$ ()A_list$ )
(declare-fun nth$ (A_list$ Nat$ )A$ )
(declare-fun less$ (Nat$ Nat$ )Bool )
(declare-fun size$ (A_list$ )Nat$ )
(declare-fun filter$ (A_bool_fun$ A_list$ )A_list$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun distinct$ (A_list$ )Bool )
(declare-fun fun_app$a (Nat_a_bool_fun_fun$ Nat$ )A_bool_fun$ )
(declare-fun fun_app$b (A_list_bool_fun$ A_list$ )Bool )
(declare-fun list_update$ (A_list$ Nat$ A$ )A_list$ )
(assert (! (not (= m$ n$ )):named a0 ))
(assert (! (distinct$ (filter$ p$ xs$ )):named a1 ))
(assert (! (less$ n$ (size$ xs$ )):named a2 ))
(assert (! (less$ m$ (size$ xs$ )):named a3 ))
(assert (! (fun_app$ p$ x$ ):named a4 ))
(assert (! (= (nth$ xs$ n$ )x$ ):named a5 ))
(assert (! (= (nth$ xs$ m$ )x$ ):named a6 ))
(assert (! (forall ((?v0 A_list$ ))(= (distinct$ ?v0 )(forall ((?v1 Nat$ ))(=> (less$ ?v1 (size$ ?v0 ))(forall ((?v2 Nat$ ))(=> (and (less$ ?v2 (size$ ?v0 ))(not (= ?v1 ?v2 )))(not (= (nth$ ?v0 ?v1 )(nth$ ?v0 ?v2 ))))))))):named a7 ))
(assert (! (forall ((?v0 A_list$ )(?v1 Nat$ )(?v2 Nat$ ))(=> (and (distinct$ ?v0 )(and (less$ ?v1 (size$ ?v0 ))(less$ ?v2 (size$ ?v0 ))))(= (= (nth$ ?v0 ?v1 )(nth$ ?v0 ?v2 ))(= ?v1 ?v2 )))):named a8 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(= (= ?v0 ?v1 )(and (= (size$ ?v0 )(size$ ?v1 ))(forall ((?v2 Nat$ ))(=> (less$ ?v2 (size$ ?v0 ))(= (nth$ ?v0 ?v2 )(nth$ ?v1 ?v2 ))))))):named a9 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat_a_bool_fun_fun$ ))(= (forall ((?v2 Nat$ ))(=> (less$ ?v2 ?v0 )(exists ((?v3 A$ ))(fun_app$ (fun_app$a ?v1 ?v2 )?v3 ))))(exists ((?v2 A_list$ ))(and (= (size$ ?v2 )?v0 )(forall ((?v3 Nat$ ))(=> (less$ ?v3 ?v0 )(fun_app$ (fun_app$a ?v1 ?v3 )(nth$ ?v2 ?v3 )))))))):named a10 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (and (= (size$ ?v0 )(size$ ?v1 ))(forall ((?v2 Nat$ ))(=> (less$ ?v2 (size$ ?v0 ))(= (nth$ ?v0 ?v2 )(nth$ ?v1 ?v2 )))))(= ?v0 ?v1 ))):named a11 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_bool_fun$ ))(=> (distinct$ ?v0 )(distinct$ (filter$ ?v1 ?v0 )))):named a12 ))
(assert (! (forall ((?v0 A_list_bool_fun$ )(?v1 A_list$ ))(=> (forall ((?v2 A_list$ ))(=> (forall ((?v3 A_list$ ))(=> (less$ (size$ ?v3 )(size$ ?v2 ))(fun_app$b ?v0 ?v3 )))(fun_app$b ?v0 ?v2 )))(fun_app$b ?v0 ?v1 ))):named a13 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list$ )(?v2 Nat$ ))(=> (and (less$ ?v0 (size$ ?v1 ))(less$ ?v2 (size$ ?v1 )))(= (distinct$ (list_update$ (list_update$ ?v1 ?v0 (nth$ ?v1 ?v2 ))?v2 (nth$ ?v1 ?v0 )))(distinct$ ?v1 )))):named a14 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (not (= (size$ ?v0 )(size$ ?v1 )))(= (= ?v0 ?v1 )false ))):named a15 ))
(assert (! (forall ((?v0 Nat$ ))(exists ((?v1 A_list$ ))(= (size$ ?v1 )?v0 ))):named a16 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (not (= (size$ ?v0 )(size$ ?v1 )))(not (= ?v0 ?v1 )))):named a17 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ ))(= (not (= ?v0 ?v1 ))(or (less$ ?v0 ?v1 )(less$ ?v1 ?v0 )))):named a18 ))
(assert (! (forall ((?v0 A_list$ )(?v1 Nat$ )(?v2 A$ )(?v3 A$ ))(= (list_update$ (list_update$ ?v0 ?v1 ?v2 )?v1 ?v3 )(list_update$ ?v0 ?v1 ?v3 ))):named a19 ))
(assert (! (forall ((?v0 A_list$ )(?v1 Nat$ )(?v2 A$ ))(= (size$ (list_update$ ?v0 ?v1 ?v2 ))(size$ ?v0 ))):named a20 ))
(assert (! (forall ((?v0 Nat$ )(?v1 Nat$ )(?v2 A_list$ )(?v3 A$ ))(=> (not (= ?v0 ?v1 ))(= (nth$ (list_update$ ?v2 ?v0 ?v3 )?v1 )(nth$ ?v2 ?v1 )))):named a21 ))
(assert (! (forall ((?v0 A_list$ )(?v1 Nat$ ))(= (list_update$ ?v0 ?v1 (nth$ ?v0 ?v1 ))?v0 )):named a22 ))
(assert (! (forall ((?v0 Nat$ )(?v1 A_list$ )(?v2 A$ ))(=> (less$ ?v0 (size$ ?v1 ))(= (nth$ (list_update$ ?v1 ?v0 ?v2 )?v0 )?v2 ))):named a23 ))
(check-sat )
;(get-unsat-core )
