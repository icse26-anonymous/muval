;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort C$ 0 )
(declare-sort D$ 0 )
(declare-sort Nat$ 0 )
(declare-sort A_a_fun$ 0 )
(declare-sort A_c_fun$ 0 )
(declare-sort B_b_fun$ 0 )
(declare-sort B_d_fun$ 0 )
(declare-sort Nat_c_fun$ 0 )
(declare-sort Nat_d_fun$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort B_bool_fun$ 0 )
(declare-sort C_bool_fun$ 0 )
(declare-sort D_bool_fun$ 0 )
(declare-sort Bool_bool_fun$ 0 )
(declare-sort A_b_bool_fun_fun$ 0 )
(declare-sort C_c_bool_fun_fun$ 0 )
(declare-sort C_d_bool_fun_fun$ 0 )
(declare-sort C_llist_bool_fun$ 0 )
(declare-sort D_c_bool_fun_fun$ 0 )
(declare-sort D_d_bool_fun_fun$ 0 )
(declare-sort D_llist_bool_fun$ 0 )
(declare-sort Bool_bool_bool_fun_fun$ 0 )
(declare-sort C_llist_c_llist_bool_fun_fun$ 0 )
(declare-sort D_llist_d_llist_bool_fun_fun$ 0 )
(declare-codatatypes ()((C_llist$ (lNil$ )(lCons$ (lhd$ C$ )(ltl$ C_llist$ )))(D_llist$ (lNil$a )(lCons$a (lhd$a D$ )(ltl$a D_llist$ )))))
(declare-fun a$ ()A_b_bool_fun_fun$ )
(declare-fun b$ ()C_d_bool_fun_fun$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()B$ )
(declare-fun uu$ ()D_d_bool_fun_fun$ )
(declare-fun uua$ ()D_llist_d_llist_bool_fun_fun$ )
(declare-fun uub$ ()C_c_bool_fun_fun$ )
(declare-fun uuc$ ()C_llist_c_llist_bool_fun_fun$ )
(declare-fun uud$ ()Bool_bool_bool_fun_fun$ )
(declare-fun lHD1$ ()A_c_fun$ )
(declare-fun lHD2$ ()B_d_fun$ )
(declare-fun lTL1$ ()A_a_fun$ )
(declare-fun lTL2$ ()B_b_fun$ )
(declare-fun lnull$ (C_llist$ )Bool )
(declare-fun lnull$a (D_llist$ )Bool )
(declare-fun transp$ (D_d_bool_fun_fun$ )Bool )
(declare-fun fun_app$ (D_llist_bool_fun$ D_llist$ )Bool )
(declare-fun rel_fun$ (A_b_bool_fun_fun$ C_d_bool_fun_fun$ A_c_fun$ B_d_fun$ )Bool )
(declare-fun transp$a (C_c_bool_fun_fun$ )Bool )
(declare-fun fun_app$a (D_llist_d_llist_bool_fun_fun$ D_llist$ )D_llist_bool_fun$ )
(declare-fun fun_app$b (C_llist_bool_fun$ C_llist$ )Bool )
(declare-fun fun_app$c (C_llist_c_llist_bool_fun_fun$ C_llist$ )C_llist_bool_fun$ )
(declare-fun fun_app$d (Bool_bool_fun$ Bool )Bool )
(declare-fun fun_app$e (Bool_bool_bool_fun_fun$ Bool )Bool_bool_fun$ )
(declare-fun fun_app$f (D_bool_fun$ D$ )Bool )
(declare-fun fun_app$g (D_d_bool_fun_fun$ D$ )D_bool_fun$ )
(declare-fun fun_app$h (C_bool_fun$ C$ )Bool )
(declare-fun fun_app$i (C_c_bool_fun_fun$ C$ )C_bool_fun$ )
(declare-fun fun_app$j (B_bool_fun$ B$ )Bool )
(declare-fun fun_app$k (A_b_bool_fun_fun$ A$ )B_bool_fun$ )
(declare-fun fun_app$l (D_c_bool_fun_fun$ D$ )C_bool_fun$ )
(declare-fun fun_app$m (C_d_bool_fun_fun$ C$ )D_bool_fun$ )
(declare-fun fun_app$n (Nat_c_fun$ Nat$ )C$ )
(declare-fun fun_app$o (Nat_d_fun$ Nat$ )D$ )
(declare-fun fun_app$p (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$q (A_c_fun$ A$ )C$ )
(declare-fun fun_app$r (A_a_fun$ A$ )A$ )
(declare-fun fun_app$s (B_d_fun$ B$ )D$ )
(declare-fun fun_app$t (B_b_fun$ B$ )B$ )
(declare-fun iS_LNIL1$ ()A_bool_fun$ )
(declare-fun iS_LNIL2$ ()B_bool_fun$ )
(declare-fun rel_fun$a (A_b_bool_fun_fun$ Bool_bool_bool_fun_fun$ A_bool_fun$ B_bool_fun$ )Bool )
(declare-fun rel_fun$b (A_b_bool_fun_fun$ A_b_bool_fun_fun$ A_a_fun$ B_b_fun$ )Bool )
(declare-fun inf_llist$ (Nat_c_fun$ )C_llist$ )
(declare-fun inf_llist$a (Nat_d_fun$ )D_llist$ )
(declare-fun llist_all2$ (C_d_bool_fun_fun$ C_llist$ )D_llist_bool_fun$ )
(declare-fun llist_all2$a (D_d_bool_fun_fun$ )D_llist_d_llist_bool_fun_fun$ )
(declare-fun llist_all2$b (C_c_bool_fun_fun$ )C_llist_c_llist_bool_fun_fun$ )
(declare-fun llist_all2$c (D_c_bool_fun_fun$ D_llist$ )C_llist_bool_fun$ )
(declare-fun unfold_llist$ (A_bool_fun$ A_c_fun$ A_a_fun$ A$ )C_llist$ )
(declare-fun unfold_llist$a (B_bool_fun$ B_d_fun$ B_b_fun$ B$ )D_llist$ )
(assert (! (forall ((?v0 D_llist$ )(?v1 D_llist$ ))(! (= (fun_app$ (fun_app$a uua$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$ (fun_app$a uua$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 C_llist$ )(?v1 C_llist$ ))(! (= (fun_app$b (fun_app$c uuc$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$b (fun_app$c uuc$ ?v0 )?v1 )))):named a1 ))
(assert (! (forall ((?v0 Bool )(?v1 Bool ))(! (= (fun_app$d (fun_app$e uud$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$d (fun_app$e uud$ ?v0 )?v1 )))):named a2 ))
(assert (! (forall ((?v0 D$ )(?v1 D$ ))(! (= (fun_app$f (fun_app$g uu$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$f (fun_app$g uu$ ?v0 )?v1 )))):named a3 ))
(assert (! (forall ((?v0 C$ )(?v1 C$ ))(! (= (fun_app$h (fun_app$i uub$ ?v0 )?v1 )(= ?v0 ?v1 )):pattern ((fun_app$h (fun_app$i uub$ ?v0 )?v1 )))):named a4 ))
(assert (! (not (fun_app$ (llist_all2$ b$ (unfold_llist$ iS_LNIL1$ lHD1$ lTL1$ x$ ))(unfold_llist$a iS_LNIL2$ lHD2$ lTL2$ y$ ))):named a5 ))
(assert (! (fun_app$j (fun_app$k a$ x$ )y$ ):named a6 ))
(assert (! (= (llist_all2$a uu$ )uua$ ):named a7 ))
(assert (! (= (llist_all2$b uub$ )uuc$ ):named a8 ))
(assert (! (forall ((?v0 D_d_bool_fun_fun$ )(?v1 D_llist$ )(?v2 D_llist$ )(?v3 D_d_bool_fun_fun$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v2 )(forall ((?v4 D$ )(?v5 D$ ))(=> (fun_app$f (fun_app$g ?v0 ?v4 )?v5 )(fun_app$f (fun_app$g ?v3 ?v4 )?v5 ))))(fun_app$ (fun_app$a (llist_all2$a ?v3 )?v1 )?v2 ))):named a9 ))
(assert (! (forall ((?v0 D_c_bool_fun_fun$ )(?v1 D_llist$ )(?v2 C_llist$ )(?v3 D_c_bool_fun_fun$ ))(=> (and (fun_app$b (llist_all2$c ?v0 ?v1 )?v2 )(forall ((?v4 D$ )(?v5 C$ ))(=> (fun_app$h (fun_app$l ?v0 ?v4 )?v5 )(fun_app$h (fun_app$l ?v3 ?v4 )?v5 ))))(fun_app$b (llist_all2$c ?v3 ?v1 )?v2 ))):named a10 ))
(assert (! (forall ((?v0 C_c_bool_fun_fun$ )(?v1 C_llist$ )(?v2 C_llist$ )(?v3 C_c_bool_fun_fun$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v2 )(forall ((?v4 C$ )(?v5 C$ ))(=> (fun_app$h (fun_app$i ?v0 ?v4 )?v5 )(fun_app$h (fun_app$i ?v3 ?v4 )?v5 ))))(fun_app$b (fun_app$c (llist_all2$b ?v3 )?v1 )?v2 ))):named a11 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 C_llist$ )(?v2 D_llist$ )(?v3 C_d_bool_fun_fun$ ))(=> (and (fun_app$ (llist_all2$ ?v0 ?v1 )?v2 )(forall ((?v4 C$ )(?v5 D$ ))(=> (fun_app$f (fun_app$m ?v0 ?v4 )?v5 )(fun_app$f (fun_app$m ?v3 ?v4 )?v5 ))))(fun_app$ (llist_all2$ ?v3 ?v1 )?v2 ))):named a12 ))
(assert (! (rel_fun$ a$ b$ lHD1$ lHD2$ ):named a13 ))
(assert (! (rel_fun$a a$ uud$ iS_LNIL1$ iS_LNIL2$ ):named a14 ))
(assert (! (rel_fun$b a$ a$ lTL1$ lTL2$ ):named a15 ))
(assert (! (forall ((?v0 C_c_bool_fun_fun$ )(?v1 Nat_c_fun$ )(?v2 Nat_c_fun$ ))(= (fun_app$b (fun_app$c (llist_all2$b ?v0 )(inf_llist$ ?v1 ))(inf_llist$ ?v2 ))(forall ((?v3 Nat$ ))(fun_app$h (fun_app$i ?v0 (fun_app$n ?v1 ?v3 ))(fun_app$n ?v2 ?v3 ))))):named a16 ))
(assert (! (forall ((?v0 D_c_bool_fun_fun$ )(?v1 Nat_d_fun$ )(?v2 Nat_c_fun$ ))(= (fun_app$b (llist_all2$c ?v0 (inf_llist$a ?v1 ))(inf_llist$ ?v2 ))(forall ((?v3 Nat$ ))(fun_app$h (fun_app$l ?v0 (fun_app$o ?v1 ?v3 ))(fun_app$n ?v2 ?v3 ))))):named a17 ))
(assert (! (forall ((?v0 D_d_bool_fun_fun$ )(?v1 Nat_d_fun$ )(?v2 Nat_d_fun$ ))(= (fun_app$ (fun_app$a (llist_all2$a ?v0 )(inf_llist$a ?v1 ))(inf_llist$a ?v2 ))(forall ((?v3 Nat$ ))(fun_app$f (fun_app$g ?v0 (fun_app$o ?v1 ?v3 ))(fun_app$o ?v2 ?v3 ))))):named a18 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 Nat_c_fun$ )(?v2 Nat_d_fun$ ))(= (fun_app$ (llist_all2$ ?v0 (inf_llist$ ?v1 ))(inf_llist$a ?v2 ))(forall ((?v3 Nat$ ))(fun_app$f (fun_app$m ?v0 (fun_app$n ?v1 ?v3 ))(fun_app$o ?v2 ?v3 ))))):named a19 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_c_fun$ )(?v2 A_a_fun$ )(?v3 A$ )(?v4 C$ )(?v5 C_llist$ ))(= (= (unfold_llist$ ?v0 ?v1 ?v2 ?v3 )(lCons$ ?v4 ?v5 ))(and (not (fun_app$p ?v0 ?v3 ))(and (= ?v4 (fun_app$q ?v1 ?v3 ))(= ?v5 (unfold_llist$ ?v0 ?v1 ?v2 (fun_app$r ?v2 ?v3 ))))))):named a20 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_d_fun$ )(?v2 B_b_fun$ )(?v3 B$ )(?v4 D$ )(?v5 D_llist$ ))(= (= (unfold_llist$a ?v0 ?v1 ?v2 ?v3 )(lCons$a ?v4 ?v5 ))(and (not (fun_app$j ?v0 ?v3 ))(and (= ?v4 (fun_app$s ?v1 ?v3 ))(= ?v5 (unfold_llist$a ?v0 ?v1 ?v2 (fun_app$t ?v2 ?v3 ))))))):named a21 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_c_fun$ )(?v2 A_a_fun$ )(?v3 A$ ))(= (not (lnull$ (unfold_llist$ ?v0 ?v1 ?v2 ?v3 )))(not (fun_app$p ?v0 ?v3 )))):named a22 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_d_fun$ )(?v2 B_b_fun$ )(?v3 B$ ))(= (not (lnull$a (unfold_llist$a ?v0 ?v1 ?v2 ?v3 )))(not (fun_app$j ?v0 ?v3 )))):named a23 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_c_fun$ )(?v2 A_a_fun$ )(?v3 A$ ))(= (lnull$ (unfold_llist$ ?v0 ?v1 ?v2 ?v3 ))(fun_app$p ?v0 ?v3 ))):named a24 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B_d_fun$ )(?v2 B_b_fun$ )(?v3 B$ ))(= (lnull$a (unfold_llist$a ?v0 ?v1 ?v2 ?v3 ))(fun_app$j ?v0 ?v3 ))):named a25 ))
(assert (! (forall ((?v0 D_d_bool_fun_fun$ )(?v1 D_llist$ )(?v2 D_llist$ )(?v3 D_llist$ ))(=> (and (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v2 )(and (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v2 )?v3 )(transp$ ?v0 )))(fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )?v3 ))):named a26 ))
(assert (! (forall ((?v0 C_c_bool_fun_fun$ )(?v1 C_llist$ )(?v2 C_llist$ )(?v3 C_llist$ ))(=> (and (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v2 )(and (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v2 )?v3 )(transp$a ?v0 )))(fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )?v3 ))):named a27 ))
(assert (! (forall ((?v0 D_d_bool_fun_fun$ )(?v1 D_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$a ?v0 )?v1 )lNil$a )(= ?v1 lNil$a )):pattern ((fun_app$a (llist_all2$a ?v0 )?v1 )))):named a28 ))
(assert (! (forall ((?v0 D_c_bool_fun_fun$ )(?v1 D_llist$ ))(! (= (fun_app$b (llist_all2$c ?v0 ?v1 )lNil$ )(= ?v1 lNil$a )):pattern ((llist_all2$c ?v0 ?v1 )))):named a29 ))
(assert (! (forall ((?v0 C_c_bool_fun_fun$ )(?v1 C_llist$ ))(! (= (fun_app$b (fun_app$c (llist_all2$b ?v0 )?v1 )lNil$ )(= ?v1 lNil$ )):pattern ((fun_app$c (llist_all2$b ?v0 )?v1 )))):named a30 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 C_llist$ ))(! (= (fun_app$ (llist_all2$ ?v0 ?v1 )lNil$a )(= ?v1 lNil$ )):pattern ((llist_all2$ ?v0 ?v1 )))):named a31 ))
(assert (! (forall ((?v0 D_d_bool_fun_fun$ )(?v1 D_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$a ?v0 )lNil$a )?v1 )(= ?v1 lNil$a )):pattern ((fun_app$ (fun_app$a (llist_all2$a ?v0 )lNil$a )?v1 )))):named a32 ))
(assert (! (forall ((?v0 D_c_bool_fun_fun$ )(?v1 C_llist$ ))(! (= (fun_app$b (llist_all2$c ?v0 lNil$a )?v1 )(= ?v1 lNil$ )):pattern ((fun_app$b (llist_all2$c ?v0 lNil$a )?v1 )))):named a33 ))
(assert (! (forall ((?v0 C_c_bool_fun_fun$ )(?v1 C_llist$ ))(! (= (fun_app$b (fun_app$c (llist_all2$b ?v0 )lNil$ )?v1 )(= ?v1 lNil$ )):pattern ((fun_app$b (fun_app$c (llist_all2$b ?v0 )lNil$ )?v1 )))):named a34 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 D_llist$ ))(! (= (fun_app$ (llist_all2$ ?v0 lNil$ )?v1 )(= ?v1 lNil$a )):pattern ((fun_app$ (llist_all2$ ?v0 lNil$ )?v1 )))):named a35 ))
(assert (! (forall ((?v0 D_d_bool_fun_fun$ )(?v1 D$ )(?v2 D_llist$ )(?v3 D$ )(?v4 D_llist$ ))(! (= (fun_app$ (fun_app$a (llist_all2$a ?v0 )(lCons$a ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))(and (fun_app$f (fun_app$g ?v0 ?v1 )?v3 )(fun_app$ (fun_app$a (llist_all2$a ?v0 )?v2 )?v4 ))):pattern ((fun_app$ (fun_app$a (llist_all2$a ?v0 )(lCons$a ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))))):named a36 ))
(assert (! (forall ((?v0 D_c_bool_fun_fun$ )(?v1 D$ )(?v2 D_llist$ )(?v3 C$ )(?v4 C_llist$ ))(! (= (fun_app$b (llist_all2$c ?v0 (lCons$a ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))(and (fun_app$h (fun_app$l ?v0 ?v1 )?v3 )(fun_app$b (llist_all2$c ?v0 ?v2 )?v4 ))):pattern ((fun_app$b (llist_all2$c ?v0 (lCons$a ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))))):named a37 ))
(assert (! (forall ((?v0 C_c_bool_fun_fun$ )(?v1 C$ )(?v2 C_llist$ )(?v3 C$ )(?v4 C_llist$ ))(! (= (fun_app$b (fun_app$c (llist_all2$b ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))(and (fun_app$h (fun_app$i ?v0 ?v1 )?v3 )(fun_app$b (fun_app$c (llist_all2$b ?v0 )?v2 )?v4 ))):pattern ((fun_app$b (fun_app$c (llist_all2$b ?v0 )(lCons$ ?v1 ?v2 ))(lCons$ ?v3 ?v4 ))))):named a38 ))
(assert (! (forall ((?v0 C_d_bool_fun_fun$ )(?v1 C$ )(?v2 C_llist$ )(?v3 D$ )(?v4 D_llist$ ))(! (= (fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))(and (fun_app$f (fun_app$m ?v0 ?v1 )?v3 )(fun_app$ (llist_all2$ ?v0 ?v2 )?v4 ))):pattern ((fun_app$ (llist_all2$ ?v0 (lCons$ ?v1 ?v2 ))(lCons$a ?v3 ?v4 ))))):named a39 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A$ )(?v2 A_c_fun$ )(?v3 A_a_fun$ ))(! (=> (fun_app$p ?v0 ?v1 )(= (unfold_llist$ ?v0 ?v2 ?v3 ?v1 )lNil$ )):pattern ((unfold_llist$ ?v0 ?v2 ?v3 ?v1 )))):named a40 ))
(assert (! (forall ((?v0 B_bool_fun$ )(?v1 B$ )(?v2 B_d_fun$ )(?v3 B_b_fun$ ))(! (=> (fun_app$j ?v0 ?v1 )(= (unfold_llist$a ?v0 ?v2 ?v3 ?v1 )lNil$a )):pattern ((unfold_llist$a ?v0 ?v2 ?v3 ?v1 )))):named a41 ))
(assert (! (forall ((?v0 D$ )(?v1 D_llist$ )(?v2 D$ )(?v3 D_llist$ ))(= (= (lCons$a ?v0 ?v1 )(lCons$a ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a42 ))
(assert (! (forall ((?v0 C$ )(?v1 C_llist$ )(?v2 C$ )(?v3 C_llist$ ))(= (= (lCons$ ?v0 ?v1 )(lCons$ ?v2 ?v3 ))(and (= ?v0 ?v2 )(= ?v1 ?v3 )))):named a43 ))
(assert (! (forall ((?v0 Nat_c_fun$ )(?v1 Nat_c_fun$ ))(= (= (inf_llist$ ?v0 )(inf_llist$ ?v1 ))(= ?v0 ?v1 ))):named a44 ))
(assert (! (forall ((?v0 Nat_d_fun$ )(?v1 Nat_d_fun$ ))(= (= (inf_llist$a ?v0 )(inf_llist$a ?v1 ))(= ?v0 ?v1 ))):named a45 ))
(check-sat )
;(get-unsat-core )
