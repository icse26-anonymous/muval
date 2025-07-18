;(set-option :produce-unsat-cores true )
(set-logic ALL_SUPPORTED )
(declare-sort A$ 0 )
(declare-sort B$ 0 )
(declare-sort A_set$ 0 )
(declare-sort A_bool_fun$ 0 )
(declare-sort A_a_bool_fun_fun$ 0 )
(declare-sort A_b_rbt_bool_fun$ 0 )
(declare-sort Color$ 0)
(declare-sort A_b_rbt$ 0)
(declare-fun r$ ()Color$)
(declare-fun b$ ()Color$)
(declare-fun empty$ ()A_b_rbt$)
(declare-fun select$ (A_b_rbt$)Color$)
(declare-fun selecta$ (A_b_rbt$)A_b_rbt$)
(declare-fun selectb$ (A_b_rbt$)A$)
(declare-fun selectc$ (A_b_rbt$)B$)
(declare-fun selectd$ (A_b_rbt$)A_b_rbt$)
(declare-fun branch$ (Color$ A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$)
(declare-fun c$ ()A_b_rbt$ )
(declare-fun k$ ()A$ )
(declare-fun l$ ()A_b_rbt$ )
(declare-fun s$ ()B$ )
(declare-fun t$ ()B$ )
(declare-fun w$ ()B$ )
(declare-fun x$ ()A$ )
(declare-fun y$ ()A$ )
(declare-fun z$ ()A$ )
(declare-fun b$a ()A_b_rbt$ )
(declare-fun r$a ()A_b_rbt$ )
(declare-fun uu$ (A_set$ )A_bool_fun$ )
(declare-fun va$ ()A_b_rbt$ )
(declare-fun vb$ ()A$ )
(declare-fun vc$ ()A_b_rbt$ )
(declare-fun vd$ ()A_b_rbt$ )
(declare-fun ve$ ()A$ )
(declare-fun vf$ ()A_b_rbt$ )
(declare-fun vg$ ()B$ )
(declare-fun uua$ (A$ )A_bool_fun$ )
(declare-fun vii$ ()B$ )
(declare-fun less$ ()A_a_bool_fun_fun$ )
(declare-fun is_rbt$ (A_a_bool_fun_fun$ A_b_rbt$ )Bool )
(declare-fun member$ (A$ A_set$ )Bool )
(declare-fun balance$ (A_b_rbt$ A$ B$ A_b_rbt$ )A_b_rbt$ )
(declare-fun collect$ (A_bool_fun$ )A_set$ )
(declare-fun fun_app$ (A_bool_fun$ A$ )Bool )
(declare-fun fun_app$a (A_a_bool_fun_fun$ A$ )A_bool_fun$ )
(declare-fun fun_app$b (A_b_rbt_bool_fun$ A_b_rbt$ )Bool )
(declare-fun lessThan$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun rbt_less$ (A_a_bool_fun_fun$ A$ )A_b_rbt_bool_fun$ )
(declare-fun rbt_sorted$ (A_a_bool_fun_fun$ A_b_rbt$ )Bool )
(declare-fun greaterThan$ (A_a_bool_fun_fun$ A$ )A_set$ )
(declare-fun rbt_greater$ (A_a_bool_fun_fun$ A$ )A_b_rbt_bool_fun$ )
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(! (= (fun_app$ (uua$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 )):pattern ((fun_app$ (uua$ ?v0 )?v1 )))):named a0 ))
(assert (! (forall ((?v0 A_set$ )(?v1 A$ ))(! (= (fun_app$ (uu$ ?v0 )?v1 )(member$ ?v1 ?v0 )):pattern ((fun_app$ (uu$ ?v0 )?v1 )))):named a1 ))
(assert (! (not (rbt_sorted$ less$ (balance$ (branch$ b$ va$ vb$ vg$ vc$ )x$ w$ (branch$ r$ (branch$ r$ b$a y$ s$ c$ )z$ t$ (branch$ b$ vd$ ve$ vii$ vf$ ))))):named a2 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (not (fun_app$ (fun_app$a less$ ?v0 )?v1 ))(or (fun_app$ (fun_app$a less$ ?v1 )?v0 )(= ?v0 ?v1 )))):named a3 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (not (= ?v0 ?v1 ))(or (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a4 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )false )(and (=> (= ?v0 ?v1 )false )(=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )false )))false )):named a5 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(=> (not false )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))false )):named a6 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a7 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a8 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v2 )?v0 ))(fun_app$ (fun_app$a less$ ?v2 )?v1 ))):named a9 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a10 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a11 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 ))false )):named a12 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= ?v1 ?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a13 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (= ?v1 ?v0 )false ))):named a14 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (= ?v0 ?v1 )false ))):named a15 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 Bool ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )?v2 )true ))):named a16 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(= (not (fun_app$ (fun_app$a less$ ?v1 )?v0 ))true ))):named a17 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a18 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (= ?v0 ?v1 )))):named a19 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (= ?v0 ?v1 )))):named a20 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )(not (= ?v1 ?v0 )))):named a21 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A$ ))(=> (and (= ?v0 ?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v2 ))(fun_app$ (fun_app$a less$ ?v0 )?v2 ))):named a22 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (not (fun_app$ (fun_app$a less$ ?v0 )?v1 ))(= (not (fun_app$ (fun_app$a less$ ?v1 )?v0 ))(= ?v1 ?v0 )))):named a23 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(=> (and (not (= ?v0 ?v1 ))(and (=> (fun_app$ (fun_app$a less$ ?v0 )?v1 )false )(=> (fun_app$ (fun_app$a less$ ?v1 )?v0 )false )))false )):named a24 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(or (fun_app$ (fun_app$a less$ ?v0 )?v1 )(or (= ?v0 ?v1 )(fun_app$ (fun_app$a less$ ?v1 )?v0 )))):named a25 ))
(assert (! (forall ((?v0 A$ ))(not (fun_app$ (fun_app$a less$ ?v0 )?v0 ))):named a26 ))
(assert (! (forall ((?v0 A$ ))(not (fun_app$ (fun_app$a less$ ?v0 )?v0 ))):named a27 ))
(assert (! (rbt_sorted$ less$ l$ ):named a28 ))
(assert (! (rbt_sorted$ less$ r$a ):named a29 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_rbt$ )(?v2 A$ ))(=> (and (fun_app$b (rbt_less$ less$ ?v0 )?v1 )(fun_app$ (fun_app$a less$ ?v0 )?v2 ))(fun_app$b (rbt_less$ less$ ?v2 )?v1 ))):named a30 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ )(?v2 A_b_rbt$ ))(=> (and (fun_app$ (fun_app$a less$ ?v0 )?v1 )(fun_app$b (rbt_greater$ less$ ?v1 )?v2 ))(fun_app$b (rbt_greater$ less$ ?v0 )?v2 ))):named a31 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ )(?v5 Color$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(= (= (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )(branch$ ?v5 ?v6 ?v7 ?v8 ?v9 ))(and (= ?v0 ?v5 )(and (= ?v1 ?v6 )(and (= ?v2 ?v7 )(and (= ?v3 ?v8 )(= ?v4 ?v9 ))))))):named a32 ))
(assert (! (fun_app$b (rbt_less$ less$ k$ )l$ ):named a33 ))
(assert (! (fun_app$b (rbt_greater$ less$ k$ )r$a ):named a34 ))
(assert (! (rbt_sorted$ less$ (branch$ b$ va$ vb$ vg$ vc$ )):named a35 ))
(assert (! (fun_app$b (rbt_less$ less$ y$ )(branch$ b$ va$ vb$ vg$ vc$ )):named a36 ))
(assert (! (fun_app$b (rbt_greater$ less$ y$ )(branch$ b$ vd$ ve$ vii$ vf$ )):named a37 ))
(assert (! (fun_app$b (rbt_less$ less$ x$ )(branch$ b$ va$ vb$ vg$ vc$ )):named a38 ))
(assert (! (rbt_sorted$ less$ (branch$ r$ (branch$ r$ b$a y$ s$ c$ )z$ t$ (branch$ b$ vd$ ve$ vii$ vf$ ))):named a39 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(! (= (rbt_sorted$ less$ (branch$ ?v0 ?v1 ?v2 ?v3 ?v4 ))(and (fun_app$b (rbt_less$ less$ ?v2 )?v1 )(and (fun_app$b (rbt_greater$ less$ ?v2 )?v4 )(and (rbt_sorted$ less$ ?v1 )(rbt_sorted$ less$ ?v4 ))))):pattern ((branch$ ?v0 ?v1 ?v2 ?v3 ?v4 )))):named a40 ))
(assert (! (fun_app$b (rbt_greater$ less$ x$ )(branch$ r$ (branch$ r$ b$a y$ s$ c$ )z$ t$ (branch$ b$ vd$ ve$ vii$ vf$ ))):named a41 ))
(assert (! (forall ((?v0 A_b_rbt$ ))(=> (is_rbt$ less$ ?v0 )(rbt_sorted$ less$ ?v0 ))):named a42 ))
(assert (! (and (fun_app$ (fun_app$a less$ x$ )y$ )(fun_app$b (rbt_less$ less$ x$ )(branch$ b$ va$ vb$ vg$ vc$ ))):named a43 ))
(assert (! (and (fun_app$ (fun_app$a less$ y$ )z$ )(fun_app$b (rbt_greater$ less$ z$ )(branch$ b$ vd$ ve$ vii$ vf$ ))):named a44 ))
(assert (! (forall ((?v0 Color$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ )(?v5 A$ )(?v6 B$ )(?v7 A_b_rbt$ )(?v8 A$ )(?v9 B$ )(?v10 A_b_rbt$ )(?v11 A$ )(?v12 B$ )(?v13 A_b_rbt$ )(?v14 A$ )(?v15 B$ )(?v16 A_b_rbt$ ))(! (= (balance$ (branch$ ?v0 (branch$ b$ ?v1 ?v2 ?v3 ?v4 )?v5 ?v6 (branch$ b$ ?v7 ?v8 ?v9 ?v10 ))?v11 ?v12 (branch$ b$ ?v13 ?v14 ?v15 ?v16 ))(branch$ b$ (branch$ ?v0 (branch$ b$ ?v1 ?v2 ?v3 ?v4 )?v5 ?v6 (branch$ b$ ?v7 ?v8 ?v9 ?v10 ))?v11 ?v12 (branch$ b$ ?v13 ?v14 ?v15 ?v16 ))):pattern ((balance$ (branch$ ?v0 (branch$ b$ ?v1 ?v2 ?v3 ?v4 )?v5 ?v6 (branch$ b$ ?v7 ?v8 ?v9 ?v10 ))?v11 ?v12 (branch$ b$ ?v13 ?v14 ?v15 ?v16 ))))):named a45 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ )(?v10 A$ )(?v11 B$ )(?v12 A_b_rbt$ ))(! (= (balance$ (branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 ))(branch$ b$ (branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 ))):pattern ((balance$ (branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 ))))):named a46 ))
(assert (! (forall ((?v0 A_bool_fun$ )(?v1 A_bool_fun$ ))(=> (forall ((?v2 A$ ))(= (fun_app$ ?v0 ?v2 )(fun_app$ ?v1 ?v2 )))(= (collect$ ?v0 )(collect$ ?v1 )))):named a47 ))
(assert (! (forall ((?v0 A_set$ ))(= (collect$ (uu$ ?v0 ))?v0 )):named a48 ))
(assert (! (forall ((?v0 A$ )(?v1 A_bool_fun$ ))(= (member$ ?v0 (collect$ ?v1 ))(fun_app$ ?v1 ?v0 ))):named a49 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 Color$ )(?v7 A_b_rbt$ )(?v8 A$ )(?v9 B$ )(?v10 A_b_rbt$ )(?v11 A$ )(?v12 B$ )(?v13 A_b_rbt$ )(?v14 A$ )(?v15 B$ )(?v16 A_b_rbt$ ))(! (= (balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ ?v6 (branch$ b$ ?v7 ?v8 ?v9 ?v10 )?v11 ?v12 (branch$ b$ ?v13 ?v14 ?v15 ?v16 )))(branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ ?v6 (branch$ b$ ?v7 ?v8 ?v9 ?v10 )?v11 ?v12 (branch$ b$ ?v13 ?v14 ?v15 ?v16 )))):pattern ((balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ ?v6 (branch$ b$ ?v7 ?v8 ?v9 ?v10 )?v11 ?v12 (branch$ b$ ?v13 ?v14 ?v15 ?v16 )))))):named a50 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ )(?v10 A$ )(?v11 B$ )(?v12 A_b_rbt$ ))(! (= (balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 )))(branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 )))):pattern ((balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 )))))):named a51 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(! (= (balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))(branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))):pattern ((balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))))):named a52 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(! (= (balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))(branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))):pattern ((balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))))):named a53 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ )(?v10 A$ )(?v11 B$ )(?v12 A_b_rbt$ )(?v13 A$ )(?v14 B$ )(?v15 A_b_rbt$ ))(! (= (balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ (branch$ r$ ?v6 ?v7 ?v8 ?v9 )?v10 ?v11 (branch$ b$ ?v12 ?v13 ?v14 ?v15 )))(branch$ r$ (branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 (branch$ b$ ?v12 ?v13 ?v14 ?v15 )))):pattern ((balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ (branch$ r$ ?v6 ?v7 ?v8 ?v9 )?v10 ?v11 (branch$ b$ ?v12 ?v13 ?v14 ?v15 )))))):named a54 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ )(?v10 A$ )(?v11 B$ )(?v12 A_b_rbt$ ))(! (= (balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ ?v6 ?v7 ?v8 (branch$ r$ ?v9 ?v10 ?v11 ?v12 )))(branch$ r$ (branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 ))):pattern ((balance$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ ?v6 ?v7 ?v8 (branch$ r$ ?v9 ?v10 ?v11 ?v12 )))))):named a55 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ )(?v10 A$ )(?v11 B$ )(?v12 A_b_rbt$ )(?v13 A$ )(?v14 B$ )(?v15 A_b_rbt$ ))(! (= (balance$ (branch$ r$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ ?v6 ?v7 ?v8 ?v9 ))?v10 ?v11 (branch$ b$ ?v12 ?v13 ?v14 ?v15 ))(branch$ r$ (branch$ b$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 (branch$ b$ ?v12 ?v13 ?v14 ?v15 )))):pattern ((balance$ (branch$ r$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ ?v6 ?v7 ?v8 ?v9 ))?v10 ?v11 (branch$ b$ ?v12 ?v13 ?v14 ?v15 ))))):named a56 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ )(?v10 A$ )(?v11 B$ )(?v12 A_b_rbt$ ))(! (= (balance$ (branch$ r$ (branch$ r$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 ))(branch$ r$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 )))):pattern ((balance$ (branch$ r$ (branch$ r$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 ?v6 )?v7 ?v8 (branch$ b$ ?v9 ?v10 ?v11 ?v12 ))))):named a57 ))
(assert (! (forall ((?v0 A_b_rbt$ )(?v1 A$ )(?v2 B$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ )(?v7 A$ )(?v8 B$ )(?v9 A_b_rbt$ ))(! (= (balance$ (branch$ r$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ ?v6 ?v7 ?v8 ?v9 ))(branch$ r$ (branch$ b$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ b$ ?v6 ?v7 ?v8 ?v9 ))):pattern ((balance$ (branch$ r$ ?v0 ?v1 ?v2 ?v3 )?v4 ?v5 (branch$ r$ ?v6 ?v7 ?v8 ?v9 ))))):named a58 ))
(assert (! (forall ((?v0 Color$ ))(=> (and (=> (= ?v0 r$ )false )(=> (= ?v0 b$ )false ))false )):named a59 ))
(assert (! (not (= r$ b$ )):named a60 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(= (fun_app$b (rbt_less$ less$ ?v0 )(balance$ ?v1 ?v2 ?v3 ?v4 ))(and (fun_app$b (rbt_less$ less$ ?v0 )?v1 )(and (fun_app$b (rbt_less$ less$ ?v0 )?v4 )(fun_app$ (fun_app$a less$ ?v2 )?v0 ))))):named a61 ))
(assert (! (forall ((?v0 A$ )(?v1 A_b_rbt$ )(?v2 A$ )(?v3 B$ )(?v4 A_b_rbt$ ))(= (fun_app$b (rbt_greater$ less$ ?v0 )(balance$ ?v1 ?v2 ?v3 ?v4 ))(and (fun_app$b (rbt_greater$ less$ ?v0 )?v1 )(and (fun_app$b (rbt_greater$ less$ ?v0 )?v4 )(fun_app$ (fun_app$a less$ ?v0 )?v2 ))))):named a62 ))
(assert (! (forall ((?v0 A$ )(?v1 Color$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(! (= (fun_app$b (rbt_less$ less$ ?v0 )(branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))(and (fun_app$ (fun_app$a less$ ?v3 )?v0 )(and (fun_app$b (rbt_less$ less$ ?v0 )?v2 )(fun_app$b (rbt_less$ less$ ?v0 )?v5 )))):pattern ((fun_app$b (rbt_less$ less$ ?v0 )(branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))))):named a63 ))
(assert (! (forall ((?v0 A$ )(?v1 Color$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(! (= (fun_app$b (rbt_greater$ less$ ?v0 )(branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))(and (fun_app$ (fun_app$a less$ ?v0 )?v3 )(and (fun_app$b (rbt_greater$ less$ ?v0 )?v2 )(fun_app$b (rbt_greater$ less$ ?v0 )?v5 )))):pattern ((fun_app$b (rbt_greater$ less$ ?v0 )(branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))))):named a64 ))
(assert (! (forall ((?v0 A$ ))(! (= (greaterThan$ less$ ?v0 )(collect$ (fun_app$a less$ ?v0 ))):pattern ((greaterThan$ less$ ?v0 )))):named a65 ))
(assert (! (forall ((?v0 A$ ))(= (lessThan$ less$ ?v0 )(collect$ (uua$ ?v0 )))):named a66 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(= (fun_app$b (rbt_less$ ?v0 ?v1 )(balance$ ?v2 ?v3 ?v4 ?v5 ))(and (fun_app$b (rbt_less$ ?v0 ?v1 )?v2 )(and (fun_app$b (rbt_less$ ?v0 ?v1 )?v5 )(fun_app$ (fun_app$a ?v0 ?v3 )?v1 ))))):named a67 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(= (fun_app$b (rbt_greater$ ?v0 ?v1 )(balance$ ?v2 ?v3 ?v4 ?v5 ))(and (fun_app$b (rbt_greater$ ?v0 ?v1 )?v2 )(and (fun_app$b (rbt_greater$ ?v0 ?v1 )?v5 )(fun_app$ (fun_app$a ?v0 ?v1 )?v3 ))))):named a68 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ ))(! (= (fun_app$b (rbt_less$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))(and (fun_app$ (fun_app$a ?v0 ?v4 )?v1 )(and (fun_app$b (rbt_less$ ?v0 ?v1 )?v3 )(fun_app$b (rbt_less$ ?v0 ?v1 )?v6 )))):pattern ((fun_app$b (rbt_less$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))))):named a69 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ )(?v2 Color$ )(?v3 A_b_rbt$ )(?v4 A$ )(?v5 B$ )(?v6 A_b_rbt$ ))(! (= (fun_app$b (rbt_greater$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))(and (fun_app$ (fun_app$a ?v0 ?v1 )?v4 )(and (fun_app$b (rbt_greater$ ?v0 ?v1 )?v3 )(fun_app$b (rbt_greater$ ?v0 ?v1 )?v6 )))):pattern ((fun_app$b (rbt_greater$ ?v0 ?v1 )(branch$ ?v2 ?v3 ?v4 ?v5 ?v6 ))))):named a70 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 Color$ )(?v2 A_b_rbt$ )(?v3 A$ )(?v4 B$ )(?v5 A_b_rbt$ ))(! (= (rbt_sorted$ ?v0 (branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))(and (fun_app$b (rbt_less$ ?v0 ?v3 )?v2 )(and (fun_app$b (rbt_greater$ ?v0 ?v3 )?v5 )(and (rbt_sorted$ ?v0 ?v2 )(rbt_sorted$ ?v0 ?v5 ))))):pattern ((rbt_sorted$ ?v0 (branch$ ?v1 ?v2 ?v3 ?v4 ?v5 ))))):named a71 ))
(assert (! (= (rbt_sorted$ less$ empty$ )true ):named a72 ))
(assert (! (is_rbt$ less$ empty$ ):named a73 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (lessThan$ less$ ?v1 ))(fun_app$ (fun_app$a less$ ?v0 )?v1 ))):named a74 ))
(assert (! (forall ((?v0 A$ )(?v1 A$ ))(= (member$ ?v0 (greaterThan$ less$ ?v1 ))(fun_app$ (fun_app$a less$ ?v1 )?v0 ))):named a75 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b (rbt_greater$ less$ ?v0 )empty$ )true ):pattern ((rbt_greater$ less$ ?v0 )))):named a76 ))
(assert (! (forall ((?v0 A$ ))(! (= (fun_app$b (rbt_less$ less$ ?v0 )empty$ )true ):pattern ((rbt_less$ less$ ?v0 )))):named a77 ))
(assert (! (forall ((?v0 A_a_bool_fun_fun$ )(?v1 A$ ))(! (= (fun_app$b (rbt_less$ ?v0 ?v1 )empty$ )true ):pattern ((rbt_less$ ?v0 ?v1 )))):named a78 ))
(check-sat )
;(get-unsat-core )
