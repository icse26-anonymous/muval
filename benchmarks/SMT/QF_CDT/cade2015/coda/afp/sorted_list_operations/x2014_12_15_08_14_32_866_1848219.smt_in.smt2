;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_set_a_set_fun$ 0 )
(declare-sort A_list$ 0)
(declare-fun nil$ ()A_list$)
(declare-fun hd$ (A_list$)A$)
(declare-fun tl$ (A_list$)A_list$)
(declare-fun cons$ (A$ A_list$ )A_list$)
(declare-fun l1$ ()A_list$ )
(declare-fun l2$ ()A_list$ )
(declare-fun inf$ (A_set$ )A_set_a_set_fun$ )
(declare-fun set$ (A_list$ )A_set$ )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun sorted$ (A_list$ )Bool )
(declare-fun fun_app$ (A_set_a_set_fun$ A_set$ )A_set$ )
(declare-fun distinct$ (A_list$ )Bool )
(declare-fun inter_sorted$ (A_list$ A_list$ )A_list$ )
(declare-fun mergesort_remdups$ (A_list$ )A_list$ )
(assert (! (not (and (distinct$ (inter_sorted$ l1$ l2$ ))(and (sorted$ (inter_sorted$ l1$ l2$ ))(= (set$ (inter_sorted$ l1$ l2$ ))(fun_app$ (inf$ (set$ l1$ ))(set$ l2$ )))))):named a0 ))
(assert (! (and (distinct$ l1$ )(sorted$ l1$ )):named a1 ))
(assert (! (and (distinct$ l2$ )(sorted$ l2$ )):named a2 ))
(assert (! (forall ((?v0 A_list$ )(?v1 A_list$ ))(=> (and (sorted$ ?v0 )(and (distinct$ ?v0 )(and (sorted$ ?v1 )(and (distinct$ ?v1 )(= (set$ ?v0 )(set$ ?v1 ))))))(= ?v0 ?v1 ))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(= (member$ ?v0 (fun_app$ (inf$ ?v1 )?v2 ))(and (member$ ?v0 ?v1 )(member$ ?v0 ?v2 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A_set$ )(?v2 A_set$ ))(=> (and (member$ ?v0 ?v1 )(member$ ?v0 ?v2 ))(member$ ?v0 (fun_app$ (inf$ ?v1 )?v2 )))):named a5 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ (fun_app$ (inf$ ?v0 )?v1 ))?v1 )(fun_app$ (inf$ ?v0 )?v1 ))):named a6 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ (fun_app$ (inf$ ?v0 )?v1 ))?v1 )(fun_app$ (inf$ ?v0 )?v1 ))):named a7 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ ?v0 )(fun_app$ (inf$ ?v0 )?v1 ))(fun_app$ (inf$ ?v0 )?v1 ))):named a8 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ ?v0 )(fun_app$ (inf$ ?v0 )?v1 ))(fun_app$ (inf$ ?v0 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$ (inf$ ?v0 )?v0 )?v0 ):pattern ((inf$ ?v0 )))):named a10 ))
(assert (! (forall ((?v0 A_set$ ))(! (= (fun_app$ (inf$ ?v0 )?v0 )?v0 ):pattern ((inf$ ?v0 )))):named a11 ))
(assert (! (forall ((?v0 A_list$ ))(and (distinct$ (mergesort_remdups$ ?v0 ))(and (sorted$ (mergesort_remdups$ ?v0 ))(= (set$ (mergesort_remdups$ ?v0 ))(set$ ?v0 ))))):named a12 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ )(?v2 A_set$ ))(= (fun_app$ (inf$ (fun_app$ (inf$ ?v0 )?v1 ))?v2 )(fun_app$ (inf$ ?v0 )(fun_app$ (inf$ ?v1 )?v2 )))):named a13 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ ?v0 )?v1 )(fun_app$ (inf$ ?v1 )?v0 ))):named a14 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A_set$ ))(= (fun_app$ (inf$ ?v0 )?v1 )(fun_app$ (inf$ ?v1 )?v0 ))):named a15 ))
(check-sat )
;(get-unsat-core )
