section \<open>Voting Power\<close>

theory Voting_Power
  imports Voting_Models
          "../Distance"
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

fun null_player :: 
  "'x set \<Rightarrow> 'v set \<Rightarrow> ('x \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> ('v, 'x) Voting_Power \<Rightarrow> bool" where
  "null_player \<M> \<V> has_swing \<delta> = (\<forall> m \<in> \<M>. \<forall> v \<in> \<V>. \<not> (has_swing m v) \<longrightarrow> \<delta> m v = 0)"

fun non_negativity :: "'x set \<Rightarrow> 'v set \<Rightarrow> ('v, 'x) Voting_Power \<Rightarrow> bool" where
  "non_negativity \<M> \<V> \<delta> = (\<forall> m \<in> \<M>. \<forall> v \<in> \<V>. \<delta> m v \<ge> 0)"

fun symmetry :: 
  "(('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set) \<Rightarrow> 'v set \<Rightarrow> 
    (('v \<Rightarrow> 'v) \<Rightarrow> 'x \<Rightarrow> 'x) \<Rightarrow> ('v, 'x) Voting_Power \<Rightarrow> bool" where
  "symmetry \<M> \<V> re \<delta> = 
    (\<forall> \<pi> \<in> Bij \<V>. \<forall> (m, f) \<in> \<M>. \<forall> v \<in> \<V>. (\<exists> f'. (re \<pi> m, f') \<in> \<M>) \<and> \<delta> m v = \<delta> (re \<pi> m) (\<pi> v))"
  (* TODO relate with is_symmetry def *)
  (* TODO relate model renaming with renaming of the tallying method f \<rightarrow> f'? *)
  (* TODO Extend to arbitrary bijective \<pi> as soon as \<V> is not considered fixed anymore *)


text \<open>
  A formal voting power index assigns real numbers to voters based on voting models.
  While the interpretation (as tallying method) can impact the definition and meaning of an index, 
  we consider the resulting formula to be applied on the level of voting model structures 'x only.
  
  TODO: Explain with examples!

  The numbers represent voters' influence on the decision process.
\<close>
locale voting_power =
  fixes
    \<V> :: "'v set" and (* TODO include \<V>, \<B>, \<O> in the changeable domain? *)
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<delta> :: "('v, 'x) Voting_Power" and
    mech :: "('v, 'b, 'o, 'x) mechanisms"
  assumes
    "\<forall> (m, f) \<in> \<M>. voting_model \<V> \<B> \<O> f"

subsection \<open>Specific Voting Power Indices\<close>

locale banzhaf_index = voting_power \<V> \<B> \<O> \<M> \<delta> mech
  for 
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<delta> :: "('v, 'x) Voting_Power" and
    mech :: "('v, 'b, 'o, 'x) mechanisms" +
  assumes
    "null_player (fst ` \<M>) \<V> (has_swing_vote mech) \<delta>" and 
    "symmetry \<M> \<V> (rename_model mech) \<delta>" and 
    "non_negativity (fst ` \<M>) \<V> \<delta>" 
    (* TODO further properties defining Banzhaf indices *)

sublocale banzhaf_index \<subseteq> voting_power
proof (unfold_locales) qed
  
subsection \<open>Equivalence of Voting Power Indices Defined on Different Models\<close>

locale power_equivalence = 
  moiso: model_set_isomorphism \<V> \<B> \<O> \<B>' \<O>' \<M> \<M>' iso mech mech' +
    pow1: voting_power \<V> \<B> \<O> \<M> \<delta> mech + pow2: voting_power \<V> \<B>' \<O>' \<M>' \<delta>' mech'
  for 
    \<V> :: "'v set" and
    \<B> :: "'b set" and \<B>' :: "'c set" and
    \<O> :: "'o set" and \<O>' :: "'u set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<M>' :: "('y \<times> (('v \<Rightarrow> 'c) \<Rightarrow> 'u)) set" and
    iso :: "'x \<Rightarrow> 'y \<Rightarrow> bool" and
    \<delta> :: "('v, 'x) Voting_Power" and
    \<delta>' :: "('v, 'y) Voting_Power" and
    mech :: "('v, 'b, 'o, 'x) mechanisms" and
    mech' :: "('v, 'c, 'u, 'y) mechanisms" +
  assumes
    coincide: 
      "\<forall> (m, f) \<in> \<M>. \<forall> (m', f') \<in> \<M>'. \<forall> v \<in> \<V>. 
        model_isomorphism \<V> \<B> \<B>' \<O> \<O>' m m' f f' mech mech' iso \<longrightarrow> \<delta> m v = \<delta>' m' v"                                       

end