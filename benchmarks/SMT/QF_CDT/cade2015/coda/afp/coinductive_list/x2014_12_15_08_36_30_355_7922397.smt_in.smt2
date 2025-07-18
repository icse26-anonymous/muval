;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort D$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_c_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort B_d_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort C_llist_set$ 0 )
(declare-sort D_llist_set$ 0 )
(declare-sort Bool_bool_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort C_d_bool_fun_fun$ 0 )
(declare-sort Bool_bool_bool_fun_fun$ 0 )
(declare-codatatypes ()((C_llist$ (lNil$ )(lCons$ (lhd$ C$ )(ltl$ C_llist$ )))(D_llist$ (lNil$a )(lCons$a (lhd$a D$ )(ltl$a D_llist$ )))))
(declare-fun a$ ()A_b_bool_fun_fun$ )
(declare-fun b$ ()C_d_bool_fun_fun$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()B$ )
(declare-fun uu$ ()Bool_bool_bool_fun_fun$ )
(declare-fun xa$ ()A$ )
(declare-fun ya$ ()B$ )
(declare-fun lHD1$ ()A_c_fun$ )
(declare-fun lHD2$ ()B_d_fun$ )
(declare-fun lTL1$ ()A_a_fun$ )
(declare-fun lTL2$ ()B_b_fun$ )
(declare-fun lnull$ (C_llist$ )Bool )
(declare-fun lnull$a (D_llist$ )Bool )
(declare-fun member$ (C_llist$ C_llist_set$ )Bool )
(declare-fun fun_app$ (Bool_bool_fun$ Bool )Bool )
(declare-fun member$a (D_llist$ D_llist_set$ )Bool )
(declare-fun rel_fun$ (A_b_bool_fun_fun$ Bool_bool_bool_fun_fun$ A_bool_fun$ B_bool_fun$ )Bool )
(declare-fun fun_app$a (Bool_bool_bool_fun_fun$ Bool )Bool_bool_fun$ )
(declare-fun fun_app$b (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$c (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$d (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$e (A_c_fun$ A$ )C$ )
(declare-fun fun_app$f (A_a_fun$ A$ )A$ )
(declare-fun fun_app$g (B_d_fun$ B$ )D$ )
(declare-fun fun_app$h (B_b_fun$ B$ )B$ )
(declare-fun iS_LNIL1$ ()A_bool_fun$ )
(declare-fun iS_LNIL2$ ()B_bool_fun$ )
(declare-fun rel_fun$a (A_b_bool_fun_fun$ A_b_bool_fun_fun$ A_a_fun$ B_b_fun$ )Bool )
(declare-fun rel_fun$b (A_b_bool_fun_fun$ C_d_bool_fun_fun$ A_c_fun$ B_d_fun$ )Bool )
(declare-fun unfold_llist$ (A_bool_fun$ A_c_fun$ A_a_fun$ A$ )C_llist$ )
(declare-fun unfold_llist$a (B_bool_fun$ B_d_fun$ B_b_fun$ B$ )D_llist$ )
(assert (! (forall ((?v0 Bool )(?v1 Bool ))(! (= (fun_app$ (fun_app$a uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uu$ ?v0 )?v1 )))):named a0 ))
(assert (! (not (= (lnull$ (unfold_llist$ iS_LNIL1$ lHD1$ lTL1$ xa$ ))(lnull$a (unfold_llist$a iS_LNIL2$ lHD2$ lTL2$ ya$ )))):named a1 ))
(assert (! (fun_app$b (fun_app$c a$ xa$ )ya$ ):named a2 ))
(assert (! (fun_app$b (fun_app$c a$ x$ )y$ ):named a3 ))
(assert (! (rel_fun$ a$ uu$ iS_LNIL1$ iS_LNIL2$ ):named a4 ))
(assert (! (rel_fun$a a$ a$ lTL1$ lTL2$ ):named a5 ))
(assert (! (rel_fun$b a$ b$ lHD1$ lHD2$ ):named a6 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_c_fun$ )(?v2 A_a_fun$ )(?v3 A$ ))(= (not (lnull$ (unfold_llist$ ?v0 ?v1 ?v2 ?v3 )))(not (fun_app$d ?v0 ?v3 )))):named a7 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_d_fun$ )(?v2 B_b_fun$ )(?v3 B$ ))(= (not (lnull$a (unfold_llist$a ?v0 ?v1 ?v2 ?v3 )))(not (fun_app$b ?v0 ?v3 )))):named a8 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_c_fun$ )(?v2 A_a_fun$ )(?v3 A$ ))(= (lnull$ (unfold_llist$ ?v0 ?v1 ?v2 ?v3 ))(fun_app$d ?v0 ?v3 ))):named a9 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_d_fun$ )(?v2 B_b_fun$ )(?v3 B$ ))(= (lnull$a (unfold_llist$a ?v0 ?v1 ?v2 ?v3 ))(fun_app$b ?v0 ?v3 ))):named a10 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 C_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a11 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 D_llist$ ))(=> (and (=> (or (lnull$ ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$ ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a12 ))
(assert (! (forall ((?v0 D_llist$ )(?v1 C_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$ ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a13 ))
(assert (! (forall ((?v0 D_llist$ )(?v1 D_llist$ ))(=> (and (=> (or (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (and (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a14 ))
(assert (! (forall ((?v0 C_llist_set$ ))(=> (and (=> (forall ((?v1 C_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 )))false )(=> (not (forall ((?v1 C_llist$ ))(=> (member$ ?v1 ?v0 )(lnull$ ?v1 ))))false ))false )):named a15 ))
(assert (! (forall ((?v0 D_llist_set$ ))(=> (and (=> (forall ((?v1 D_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$a ?v1 )))false )(=> (not (forall ((?v1 D_llist$ ))(=> (member$a ?v1 ?v0 )(lnull$a ?v1 ))))false ))false )):named a16 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 C_llist$ ))(=> (and (=> (and (lnull$ ?v0 )(lnull$ ?v1 ))false )(=> (or (not (lnull$ ?v0 ))(not (lnull$ ?v1 )))false ))false )):named a17 ))
(assert (! (forall ((?v0 D_llist$ )(?v1 D_llist$ ))(=> (and (=> (and (lnull$a ?v0 )(lnull$a ?v1 ))false )(=> (or (not (lnull$a ?v0 ))(not (lnull$a ?v1 )))false ))false )):named a18 ))
(assert (! (forall ((?v0 C_llist$ ))(=> (and (=> (lnull$ ?v0 )false )(=> (not (lnull$ ?v0 ))false ))false )):named a19 ))
(assert (! (forall ((?v0 D_llist$ ))(=> (and (=> (lnull$a ?v0 )false )(=> (not (lnull$a ?v0 ))false ))false )):named a20 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_c_fun$ )(?v3 A_a_fun$ ))(=> (not (fun_app$d ?v0 ?v1 ))(not (lnull$ (unfold_llist$ ?v0 ?v2 ?v3 ?v1 ))))):named a21 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_d_fun$ )(?v3 B_b_fun$ ))(=> (not (fun_app$b ?v0 ?v1 ))(not (lnull$a (unfold_llist$a ?v0 ?v2 ?v3 ?v1 ))))):named a22 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_c_fun$ )(?v3 A_a_fun$ ))(=> (fun_app$d ?v0 ?v1 )(lnull$ (unfold_llist$ ?v0 ?v2 ?v3 ?v1 )))):named a23 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_d_fun$ )(?v3 B_b_fun$ ))(=> (fun_app$b ?v0 ?v1 )(lnull$a (unfold_llist$a ?v0 ?v2 ?v3 ?v1 )))):named a24 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_c_fun$ )(?v2 A_a_fun$ )(?v3 A$ )(?v4 C$ )(?v5 C_llist$ ))(= (= (unfold_llist$ ?v0 ?v1 ?v2 ?v3 )(lCons$ ?v4 ?v5 ))(and (not (fun_app$d ?v0 ?v3 ))(and (= ?v4 (fun_app$e ?v1 ?v3 ))(= ?v5 (unfold_llist$ ?v0 ?v1 ?v2 (fun_app$f ?v2 ?v3 ))))))):named a25 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_d_fun$ )(?v2 B_b_fun$ )(?v3 B$ )(?v4 D$ )(?v5 D_llist$ ))(= (= (unfold_llist$a ?v0 ?v1 ?v2 ?v3 )(lCons$a ?v4 ?v5 ))(and (not (fun_app$b ?v0 ?v3 ))(and (= ?v4 (fun_app$g ?v1 ?v3 ))(= ?v5 (unfold_llist$a ?v0 ?v1 ?v2 (fun_app$h ?v2 ?v3 ))))))):named a26 ))
(check-sat )
;(get-unsat-core )
