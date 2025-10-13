section \<open>Voting Power\<close>

theory Voting_Power
  imports Voting_Models
          Distance
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Auxiliary Lemmas and Definitions\<close>

fun uncurry3 :: "('w \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('w \<times> 'x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry3 f = (\<lambda>(w,x,y). f w x y)"

fun swap_voters :: "'v \<Rightarrow> 'v \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "swap_voters v w e = 
    (let \<pi> = (\<lambda>x::'v. (if x = w then v else (if x = v then w else x))) in
      rename \<pi> e)"

fun coincide_except :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> bool" where
  "coincide_except e1 e2 v = 
      (\<forall> w \<in> (voters_\<E> e1) - {v}. profile_\<E> e1 w = profile_\<E> e2 w)"

lemma rename_inv_commute:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    "the_inv (rename \<pi>) = rename (the_inv \<pi>)"
proof -
  have "(rename (the_inv \<pi>)) \<circ> (rename \<pi>) = id"
    unfolding comp_def
    using rename_inv ext assms id_def inj_def prod_cases3 rename_inj
    by (metis (no_types, lifting))
  thus "the_inv (rename \<pi>) = rename (the_inv \<pi>)"
    using  ext assms bij_betw_the_inv_into comp_apply id_apply rename_inj the_inv_f_f
    by (metis (no_types, lifting))
qed

lemma card_orders: 
  fixes
    X :: "'x set"
  shows "finite X \<Longrightarrow> card {rel. linear_order_on X rel} = fact (card X)"
proof (induction "card X" arbitrary: X)
  case 0
  fix 
    X :: "'x set"
  assume 
    0: "0 = card X" and
    "finite X"
  hence "X = {}"
    by simp
  hence "Collect (linear_order_on X) = {{}}"
    unfolding linear_order_on_def partial_order_on_def total_on_def 
              preorder_on_def antisym_def refl_on_def trans_def
    by blast
  thus "card (Collect (linear_order_on X)) = fact (card X)"
    using 0
    by simp
next
  case (Suc x)
  fix 
    x :: nat and
    X :: "'x set"
  assume
    fin: "finite X" and
    card: "Suc x = card X" and
    hyp: 
      "\<And>(X::'x set). x = card X \<Longrightarrow> finite X \<Longrightarrow> 
                      card (Collect (linear_order_on X)) = fact (card X)"
  have "Suc x > 0"
    by blast
  hence "card X \<noteq> 0"
    using card
    by simp
  moreover have "card {} = 0"
    by simp
  ultimately have "X \<noteq> {}"
    by blast
  then obtain z :: 'x where "z \<in> X"
    by blast
  let ?Xm = "X - {z}"
  have "x = card ?Xm"
    using card
    by (simp add: \<open>z \<in> X\<close>)
  moreover have "finite ?Xm"
    using fin
    by blast
  ultimately have cardm: "card (Collect (linear_order_on ?Xm)) = fact (card ?Xm)"
    using hyp[of "?Xm"] card_partition
    by blast
  let ?extOrd = "\<lambda>p. {pi. linear_order_on X pi \<and> (pi \<inter> (?Xm \<times> ?Xm)) = p}"
  let ?ords = "{?extOrd p | p. p \<in> Collect (linear_order_on ?Xm)}"
  let ?rk = "\<lambda>x rel. card {y. (y, x) \<in> rel}"
  let ?f = "\<lambda>pi. ?rk z pi"
  have inj: "\<forall>p \<in> Collect (linear_order_on ?Xm). inj_on ?f (?extOrd p)"
    unfolding inj_on_def 
    sorry
  moreover have "\<forall>p \<in> Collect (linear_order_on ?Xm). ?f ` (?extOrd p) = {1..card X}"
    sorry
  ultimately have "\<forall>p \<in> Collect (linear_order_on ?Xm). bij_betw ?f (?extOrd p) {1..card X}"
    sorry
  hence "\<forall>p \<in> Collect (linear_order_on ?Xm). card (?extOrd p) = card {1..card X}"
    using bij_betw_same_card
    by blast
  moreover have "card {1..card X} = card X"
    using atLeast0LessThan card_lessThan 
    by simp
  ultimately have eltCard0: "\<forall>p \<in> Collect (linear_order_on ?Xm). card (?extOrd p) = card X"
    by simp
  hence eltCard:
    "\<forall> pi \<in> {?extOrd p |p. p \<in> Collect (linear_order_on (X - {z}))}. card pi = card X"
    by blast
  have 
    "\<forall>p1 \<in> Collect (linear_order_on ?Xm). \<forall>p2 \<in> Collect (linear_order_on ?Xm).
          p1 \<noteq> p2 \<longrightarrow> 
            (\<forall>pi1 \<in> (?extOrd p1). \<forall>pi2 \<in> (?extOrd p2). 
              (pi1 \<inter> (?Xm \<times> ?Xm)) \<noteq> (pi2 \<inter> (?Xm \<times> ?Xm)))"
    by simp
  hence disj0:
    "\<forall>p1 \<in> Collect (linear_order_on ?Xm). \<forall>p2 \<in> Collect (linear_order_on ?Xm).
        p1 \<noteq> p2 \<longrightarrow> ?extOrd p1 \<inter> ?extOrd p2 = {}"
    by blast
  hence disj:
    "\<forall> pi1 \<in> {?extOrd p |p. p \<in> Collect (linear_order_on (X - {z}))}.
      \<forall> pi2 \<in> {?extOrd p |p. p \<in> Collect (linear_order_on (X - {z}))}.
        pi1 \<noteq> pi2 \<longrightarrow> pi1 \<inter> pi2 = {}"
    by blast
  have "\<forall>p \<in> Collect (linear_order_on ?Xm). 
    (\<exists>pi. linear_order_on X pi \<and> (pi \<inter> ?Xm \<times> ?Xm) = p)"
    using eltCard0 \<open>card X \<noteq> 0\<close>
    by (metis (mono_tags, lifting) Collect_empty_eq card_eq_0_iff)
  hence "\<forall>p \<in> Collect (linear_order_on ?Xm). ?extOrd p \<noteq> {}"
    by simp
  hence "inj_on ?extOrd (Collect (linear_order_on ?Xm))"
    using disj0
    unfolding inj_on_def
    by (metis (lifting) inf.idem)
  moreover have "?extOrd ` (Collect (linear_order_on ?Xm)) = ?ords"
    by blast
  ultimately have "bij_betw ?extOrd (Collect (linear_order_on ?Xm)) ?ords"
    unfolding bij_betw_def
    by blast
  hence cardIndex: "card ?ords = card (Collect (linear_order_on ?Xm))"
    by (simp add: bij_betw_same_card)
  have "finite (Collect (linear_order_on ?Xm))"
    by (metis card.infinite cardm fact_nonzero)
  hence fin: "finite ?ords"
    by simp
  moreover have "\<forall>p \<in> Collect (linear_order_on ?Xm). finite (?extOrd p)"
    using \<open>card X \<noteq> 0\<close> card_eq_0_iff eltCard0 
    by force
  ultimately have finU: "finite (\<Union>?ords)"
    by blast
  have cardU: "card (\<Union>?ords) = (card X) * (fact (card ?Xm))"
    using eltCard card_partition[of ?ords "card X"] cardm disj fin finU cardIndex
    by simp
  have "\<forall>p. linear_order_on X p \<longrightarrow> linear_order_on ?Xm (p \<inter> (?Xm \<times> ?Xm))"
    unfolding linear_order_on_def partial_order_on_def total_on_def 
              preorder_on_def refl_on_def trans_def antisym_def 
    by blast
  moreover have "\<forall>p. linear_order_on X p \<longrightarrow> p \<in> ?extOrd (p \<inter> (?Xm \<times> ?Xm))"
    by simp
  ultimately have "Collect (linear_order_on X) \<subseteq> \<Union>?ords"
    by blast
  moreover have "\<Union>?ords \<subseteq> Collect (linear_order_on X)"
    by blast
  ultimately have "\<Union>?ords = Collect (linear_order_on X)"
    by blast
  hence "card (Collect (linear_order_on X)) = (card X) * (fact (card ?Xm))"
    using cardU
    by simp
  also have "(card X) * (fact (card ?Xm)) = fact (card X)"
    using \<open>x = card ?Xm\<close> card fact_Suc id_apply of_nat_eq_id
    by metis
  finally show "card (Collect (linear_order_on X)) = fact (card X)"
    by argo
qed

subsection \<open>Voting Power\<close>

type_synonym ('v, 'x) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> real"

record ('v, 'b, 'o, 'x) abstract_notions =
  has_swing_vote :: "'x \<Rightarrow> 'v \<Rightarrow> bool"
  rename_instance :: "('v \<Rightarrow> 'v) \<Rightarrow> 'x \<Rightarrow> 'x"

text \<open>
  A voting power index assigns real numbers to voters based on voting models.
  The numbers represent voters' influence on the decision process.
\<close>
locale voting_power =
  fixes
    \<V> :: "'v set" and (* TODO include \<V>, \<B>, \<O> in the changeable domain? *)
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<delta> :: "('v, 'x) Voting_Power" and
    AN :: "('v, 'b, 'o, 'x) abstract_notions" (structure) 
  assumes
    "\<forall> (m, f) \<in> \<M>. voting_model \<V> \<B> \<O> f"
begin

subsection \<open>(Abstract) Voting Power Axioms\<close>

definition null_player where
  "null_player \<equiv> (\<forall> (m, f) \<in> \<M>. \<forall> v \<in> \<V>. \<not>(has_swing_vote AN m v) \<longrightarrow> \<delta> m v = 0)"

definition non_negativity where
  "non_negativity = (\<forall> (m, f) \<in> \<M>. \<forall> v \<in> \<V>. \<delta> m v \<ge> 0)"

definition symmetry where
  "symmetry = (\<forall> \<pi> \<in> Bij \<V>. \<forall> (m, f) \<in> \<M>. \<forall> v \<in> \<V>. \<delta> m v = \<delta> (rename_instance AN \<pi> m) (\<pi> v))"
  (* TODO relate with is_symmetry def *)

end

subsection \<open>Specific Voting Power Indices\<close>

locale banzhaf_index = voting_power \<V> \<B> \<O> \<M> \<delta> AN
  for 
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<delta> :: "('v, 'x) Voting_Power" and
    AN :: "('v, 'b, 'o, 'x) abstract_notions" +
  assumes
    "null_player" and 
    "symmetry" and 
    "non_negativity" 
    (* TODO further properties defining Banzhaf indices *)

sublocale banzhaf_index \<subseteq> voting_power
proof (unfold_locales) qed
  
subsection \<open>Equivalence of Voting Power Indices Defined on Different Models\<close>

locale power_equivalence = 
  model_set_isomorphism \<V> \<B> \<O> \<M> \<M>' isomorphism +
    pow1: voting_power \<V> \<B> \<O> \<M> \<delta> AN + pow2: voting_power \<V> \<B> \<O> \<M>' \<delta>' AN'
  for 
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<M>' :: "('y \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    isomorphism :: "'x \<Rightarrow> 'y \<Rightarrow> bool" and
    \<delta> :: "('v, 'x) Voting_Power" and
    \<delta>' :: "('v, 'y) Voting_Power" and
    AN :: "('v, 'b, 'o, 'x) abstract_notions" and
    AN' :: "('v, 'b, 'o, 'y) abstract_notions" +
  assumes
    coincide: 
      "\<forall> (m, f) \<in> \<M>. \<forall> (m', f) \<in> \<M>'. \<forall> v \<in> \<V>. 
        model_isomorphism \<V> \<B> \<O> m m' f isomorphism \<longrightarrow> \<delta> m v = \<delta>' m' v"  

locale svg_rule_power_comparison = 
  power_equivalence \<V> "(UNIV::bool set)" "(UNIV::bool set)" \<M> \<M>' isomorphism \<delta> \<delta>' AN AN'
  for 
    \<V> :: "'v set" and
    \<M> :: "((('v \<Rightarrow> 'b) \<Rightarrow> 'o) \<times> (('v \<Rightarrow> bool) \<Rightarrow> bool)) set" and
    \<M>' :: "('v Simple_Voting_Game \<times> (('v \<Rightarrow> bool) \<Rightarrow> bool)) set" and
    isomorphism :: "(('v \<Rightarrow> 'b) \<Rightarrow> 'o) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" and
    \<delta> :: "('v, ('v \<Rightarrow> 'b) \<Rightarrow> 'o) Voting_Power" and
    \<delta>' :: "('v, 'v Simple_Voting_Game) Voting_Power" and
    AN :: "('v, 'b, 'o, ('v \<Rightarrow> 'b) \<Rightarrow> 'o) abstract_notions" and
    AN' :: "('v, 'b, 'o, 'v Simple_Voting_Game) abstract_notions" +
  assumes
    rules: "\<forall> (m, f) \<in> \<M>. voting_rule \<V> \<B> \<O> m" and (* and m = f? *)
    games: "\<forall> (m', f') \<in> \<M>'. simple_voting_game \<V> m'"
begin

lemma equiv_null_player: 
  "pow1.null_player \<longleftrightarrow> pow2.null_player"
  sorry

end

subsection \<open>Exemplary Instantiations\<close>

fun swing_vote :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool" where
  "swing_vote G v S = (S \<subseteq> players G \<and> value_fun G (S \<union> {v}) \<noteq> value_fun G (S \<union> {v}))"

fun \<delta>\<^sub>B\<^sub>Z :: "('v, 'v Simple_Voting_Game) Voting_Power" where
  "\<delta>\<^sub>B\<^sub>Z G v = 
    (1/2^(card (players G))) 
      * (real (card (preimg (swing_vote G v) {S. S \<subseteq> players G} True)))"

definition AN\<^sub>S\<^sub>V\<^sub>G :: "('v, bool, bool, 'v Simple_Voting_Game) abstract_notions" where
  "AN\<^sub>S\<^sub>V\<^sub>G = 
    (|
      has_swing_vote = (\<lambda> G v. v \<in> players G \<and> (\<exists> S. swing_vote G v S)), 
      rename_instance = (\<lambda> \<pi> G. (\<pi> ` (players G), (\<lambda> S. value_fun G {p \<in> players G. \<pi> p \<in> S})))
    |)" (* TODO official preimg function? *)
 
fun tally\<^sub>S\<^sub>V\<^sub>G :: "'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> bool) \<Rightarrow> bool)" where
  "tally\<^sub>S\<^sub>V\<^sub>G \<G> p = value_fun \<G> (preimg p (players \<G>) True)"

lemma classic_svg_banzhaf:
  fixes
    \<V> :: "'v set" and
    \<M> :: "'v Simple_Voting_Game set"
  assumes
    "finite \<V>"
  shows
    "banzhaf_index \<V> (UNIV::(bool set)) (UNIV::(bool set)) {(\<G>, tally\<^sub>S\<^sub>V\<^sub>G \<G>) | \<G>. \<G> \<in> \<M>} \<delta>\<^sub>B\<^sub>Z AN\<^sub>S\<^sub>V\<^sub>G" 
  sorry

end